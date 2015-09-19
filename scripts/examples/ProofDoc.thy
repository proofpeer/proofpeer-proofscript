theory ProofDoc extends \root

#
  ~paragraph This is not really necessary, but let's introduce it anyway, so that it can be used outside of contexts 
    as well.
  ~p can be used as a shortcut for ``~paragraph``.
  ~label a0h2wawdjjuk
  ~tag "functional programming" symmetric associative commutative
  ~verbatim
  ~code 
  ~code Python
  ~proofscript
  ~math
    x > 10
  This is `embedded ProofScript`. And this is how I insert inline ProofDoc generated by code: $`generating ProofScript`.
  It is also possible to insert block ProofDoc:
  ~doc 
    ....
  This is ``embedded verbatim``.
  This is ```Python embedded python```.
  Therefore ```ProofScript blabla``` is the same as `blabla`.
  This is embedded math: $$x > 10$$.
  ~ This is a toplevel header
  ~~ This is a secondlevel header
  ~~~ This is a thirdlevel header $$x > 10$$ 
  ~ulist
    - This is the first item, and when it goes to the next line,
     it must indent relative to the dash.
    - This is the second item.
  There are also ordered lists:  
  ~olist
    - This is the first item, and when it goes to the next line,
     it must indent relative to the dash.
    - This is the second item.
  ~quote 
    It's better to burn out than to fade away!
  ~quote Highlander
    It's better to burn out than to fade away!
  ~quote @obua
    It's better to burn out than to fade away!
  There are the typical ways to designate *italic* and **bold** text. 
  I can refer to user @obua just like that.
  I can point to a label with a reference like that: ~ref:a0h2wawdjjuk~
  I can point to a label within a given theory like that: ~ref:\bootstrap\classical | a0h2wawdjjuk~
  I can point to a given theory (or image, or article) like that: ~ref \bootstrap\classical~. 
  It is possible to fully qualify the theory with branch, version and location: 
    ~ref:\bootstrap\classical@main:48@proofpeer.net|a0h2wawdjjuk~.
  You can use ref not only to point to labels, but also to entities:
    ~ref \bootstrap\classical / choiceDef~.
  You can use other ways of referencing: ~doi:10.1007/978-3-319-20615-8_6~, ~arXiv:1007.3023~,
  ~http://proofpeer.net~.
  It is also possible to reference an image: ~img \bootstrap\classicalimg@main:48@proofpeer.net~
  You can link a given piece of text via [ text | link ], where link is one of the above ways of linking, for example
  ~ref a0h2wawdjjuk~.
  You can have bibliographies in the text
  ~bibliography
    - typeinferenceforzfh
      ~linktext This is the text shown by default 
      ~author Steven Obua
      ~author Jacques Fleuriot
      ~author Phil Scott
      ~author David Aspinall
      ~title Type Inference for ZFH
      ~year 2015
      ~doi:10.1007/978-3-319-20615-8_6
  And there are tables
  ~table | 10 | 20
    ~row
      - *x*
      - *y*
    ~row
      - 10
      - 20
    ~row
      - 30
      - 40

  It is also possible to display images:
  ~image 
    ~ref \bootstrap\images\hey
    ~title This is the title of the image, title and image are displayed together


