class Calculator < Liquid::Tag
  ##Syntax = /^\s*([^\s]+)(\s+(\d+)\s+(\d+)\s*)?/
  Syntax = /^\s*([^\s]+)(?:\s+(\d+)\s+(\d+)\s*)?/

  def initialize(tagName, markup, tokens)
    super

    if markup =~ Syntax then
      @id = $1

      if $2.nil? then
          @width = 560
          @height = 420
      else
          @width = $2.to_i
          @height = $3.to_i
      end
    else
      raise "No Calculator Id provided in the \"calculator\" tag"
    end
  end

  def render(context)
    "<iframe width=\"#{@width}\" height=\"#{@height}\" src=\"/Hedge-o-Mat/static/#{@id}.html\"></iframe>"
  end

  Liquid::Template.register_tag "calculator", self
end

