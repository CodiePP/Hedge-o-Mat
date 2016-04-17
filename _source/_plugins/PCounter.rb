class PCounter < Liquid::Tag
  #Syntax = /^\s*(\S+)\s*/

  def initialize(tagName, markup, tokens)
    super
  end

  def render(context)
    @id = context["page"]["id"]
    "<img src=\"http://hom.dubhe.uberspace.de/cgi-bin/num2png.cgi?/p=#{@id}\">##</img>"
  end

  Liquid::Template.register_tag "pcounter", self
end

