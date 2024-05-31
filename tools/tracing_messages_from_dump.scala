package jeha

import isabelle._
// import isabelle.{Path, Bytes /*, YXML */ }
import scala.util.matching.Regex

val timing_report_pattern: Regex = "total elapsed time until contradiction: ([0-9]+) ms".r

object Main {
  def main(args: Array[String]) = {
    // After running
    // ~/Isabelle2023/bin/isabelle dump -d ~/git/jeha -d ~/git/jeha/tests -b JEHA_TEST_BASE -B JEHA_TEST_GENERAL

    val read_path = Path.explode("~/dump/JEHA_TEST_GENERAL.misc/PIDE/messages")
    val xml = read_xml(read_path)

    val write_path_text = Path.explode("~/tmp/isabelle/JEHA_TEST_GENERAL.misc.messages")
    val () = writeTextContent(write_path_text, xml)

    val write_path_xml = Path.explode("~/tmp/isabelle/JEHA_TEST_GENERAL.misc.messages.xml")
    val () = writePseudoXml(write_path_xml, xml)

    val write_path_timings = Path.explode("~/tmp/isabelle/JEHA_TEST_GENERAL.misc.timings")
    val timings = joinLines(find_timing_reports(xml))
    val () = writeString(write_path_timings, timings)
  }

  def read_xml(path: Path): XML.Body = {
    val in_bytes = Bytes.read(path)
    // see mirabelle.scala
    val in_chars = UTF8.decode_permissive(in_bytes)
    YXML.parse_body(in_chars)
  }

  def extractText(xml: XML.Body): String = {
    val tracing_messages = xml.map(tracing_message => XML.content(tracing_message))
    joinLines(tracing_messages)
  }

  def find_timing_reports(xml: XML.Body): List[String] = {
    val text = extractText(xml)
    timing_report_pattern.findAllMatchIn(text).map(_.matched).toList
  }

  def writeTextContent(path: Path, xml: XML.Body) = {
    val text = extractText(xml)
    val () = writeString(path, text)
  }

  def writePseudoXml(path: Path, xml: XML.Body) = {
    val xml_as_string = XML.header + XML.string_of_body(xml)
    val () = writeString(path, xml_as_string)
  }

  def writeString(path: Path, text: String) = {
    val out_bytes = Bytes.apply(text)
    val () = Bytes.write(path, out_bytes)
  }

  def joinLines(lines: List[String]): String = {
    lines.mkString("\n") + "\n"
  }
}

