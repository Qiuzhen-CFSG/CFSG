module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Word

/-!
# Schreier witnesses for the first suffix point

The representatives and factors are explicit words. Each code stores its length
and its leftmost letter in the least significant hexadecimal digit. Positive
factor letters come first, followed by inverse letters. These numerical data
assert no group identities; the actual transitions must be proved in Lean.
Source: retained ATLAS F23G1-p31671B0; application GLS3 Table 5.3u.
Reproduce with `FirstPair/source/generate.py --discover`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First

def representativeCode (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              if b < 1 then
                (0, 0)
              else
                (1, 0)
            else
              if b < 3 then
                (1, 1)
              else
                if b < 4 then
                  (1, 4)
                else
                  (1, 5)
          else
            if b < 8 then
              if b < 6 then
                (1, 6)
              else
                if b < 7 then
                  (2, 0)
                else
                  (2, 4)
            else
              if b < 9 then
                (2, 5)
              else
                if b < 10 then
                  (2, 6)
                else
                  (2, 20)
        else
          if b < 16 then
            if b < 13 then
              if b < 12 then
                (2, 21)
              else
                (2, 22)
            else
              if b < 14 then
                (2, 64)
              else
                if b < 15 then
                  (2, 68)
                else
                  (2, 69)
          else
            if b < 19 then
              if b < 17 then
                (2, 70)
              else
                if b < 18 then
                  (2, 80)
                else
                  (2, 81)
            else
              if b < 20 then
                (2, 82)
              else
                if b < 21 then
                  (2, 84)
                else
                  (2, 85)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (2, 86)
              else
                (2, 96)
            else
              if b < 25 then
                (2, 98)
              else
                if b < 26 then
                  (2, 100)
                else
                  (2, 101)
          else
            if b < 30 then
              if b < 28 then
                (2, 102)
              else
                if b < 29 then
                  (3, 6)
                else
                  (3, 65)
            else
              if b < 31 then
                (3, 69)
              else
                if b < 32 then
                  (3, 70)
                else
                  (3, 80)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (3, 81)
              else
                if b < 35 then
                  (3, 86)
                else
                  (3, 96)
            else
              if b < 37 then
                (3, 97)
              else
                if b < 38 then
                  (3, 98)
                else
                  (3, 100)
          else
            if b < 42 then
              if b < 40 then
                (3, 101)
              else
                if b < 41 then
                  (3, 325)
                else
                  (3, 326)
            else
              if b < 43 then
                (3, 336)
              else
                if b < 44 then
                  (3, 337)
                else
                  (3, 341)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                (3, 342)
              else
                (3, 352)
            else
              if b < 48 then
                (3, 353)
              else
                if b < 49 then
                  (3, 357)
                else
                  (3, 358)
          else
            if b < 53 then
              if b < 51 then
                (3, 1030)
              else
                if b < 52 then
                  (3, 1094)
                else
                  (3, 1105)
            else
              if b < 54 then
                (3, 1110)
              else
                if b < 55 then
                  (3, 1120)
                else
                  (3, 1122)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (3, 1125)
              else
                (3, 1126)
            else
              if b < 59 then
                (3, 1280)
              else
                if b < 60 then
                  (3, 1286)
                else
                  (3, 1301)
          else
            if b < 64 then
              if b < 62 then
                (3, 1302)
              else
                if b < 63 then
                  (3, 1312)
                else
                  (3, 1313)
            else
              if b < 65 then
                (3, 1316)
              else
                if b < 66 then
                  (3, 1318)
                else
                  (3, 1344)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (3, 1362)
              else
                (3, 1366)
            else
              if b < 70 then
                (3, 1540)
              else
                if b < 71 then
                  (3, 1541)
                else
                  (3, 1542)
          else
            if b < 75 then
              if b < 73 then
                (3, 1568)
              else
                if b < 74 then
                  (3, 1573)
                else
                  (3, 1574)
            else
              if b < 76 then
                (3, 1604)
              else
                if b < 77 then
                  (3, 1605)
                else
                  (3, 1606)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (3, 1616)
              else
                if b < 80 then
                  (3, 1621)
                else
                  (3, 1622)
            else
              if b < 82 then
                (3, 1633)
              else
                if b < 83 then
                  (3, 1637)
                else
                  (3, 1638)
          else
            if b < 87 then
              if b < 85 then
                (4, 96)
              else
                if b < 86 then
                  (4, 97)
                else
                  (4, 98)
            else
              if b < 88 then
                (4, 100)
              else
                if b < 89 then
                  (4, 101)
                else
                  (4, 102)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (4, 1046)
              else
                (4, 1302)
            else
              if b < 93 then
                (4, 1382)
              else
                if b < 94 then
                  (4, 1540)
                else
                  (4, 1541)
          else
            if b < 98 then
              if b < 96 then
                (4, 1552)
              else
                if b < 97 then
                  (4, 1553)
                else
                  (4, 1556)
            else
              if b < 99 then
                (4, 1558)
              else
                if b < 100 then
                  (4, 1569)
                else
                  (4, 1573)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (4, 1574)
              else
                (4, 1600)
            else
              if b < 104 then
                (4, 1606)
              else
                if b < 105 then
                  (4, 1617)
                else
                  (4, 1618)
          else
            if b < 109 then
              if b < 107 then
                (4, 5200)
              else
                if b < 108 then
                  (4, 5216)
                else
                  (4, 5220)
            else
              if b < 110 then
                (4, 5221)
              else
                if b < 111 then
                  (4, 5222)
                else
                  (4, 5380)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (4, 5382)
              else
                (4, 5398)
            else
              if b < 115 then
                (4, 5477)
              else
                if b < 116 then
                  (4, 5478)
                else
                  (4, 5632)
          else
            if b < 120 then
              if b < 118 then
                (4, 5638)
              else
                if b < 119 then
                  (4, 5653)
                else
                  (4, 5654)
            else
              if b < 121 then
                (4, 5712)
              else
                if b < 122 then
                  (4, 5713)
                else
                  (4, 5716)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (4, 5733)
              else
                if b < 125 then
                  (4, 16482)
                else
                  (4, 16484)
            else
              if b < 127 then
                (4, 16486)
              else
                if b < 128 then
                  (4, 17504)
                else
                  (4, 17505)
          else
            if b < 132 then
              if b < 130 then
                (4, 17506)
              else
                if b < 131 then
                  (4, 17508)
                else
                  (4, 17509)
            else
              if b < 133 then
                (4, 17764)
              else
                if b < 134 then
                  (4, 17765)
                else
                  (4, 17766)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (4, 17920)
              else
                (4, 17926)
            else
              if b < 138 then
                (4, 17958)
              else
                if b < 139 then
                  (4, 18000)
                else
                  (4, 18001)
          else
            if b < 143 then
              if b < 141 then
                (4, 18004)
              else
                if b < 142 then
                  (4, 20820)
                else
                  (4, 20832)
            else
              if b < 144 then
                (4, 21012)
              else
                if b < 145 then
                  (4, 21014)
                else
                  (4, 21056)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (4, 21088)
              else
                (4, 21510)
            else
              if b < 149 then
                (4, 21798)
              else
                if b < 150 then
                  (4, 21857)
                else
                  (4, 24645)
          else
            if b < 154 then
              if b < 152 then
                (4, 24660)
              else
                if b < 153 then
                  (4, 24661)
                else
                  (4, 24676)
            else
              if b < 155 then
                (4, 25173)
              else
                if b < 156 then
                  (4, 25174)
                else
                  (4, 25185)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (4, 25189)
              else
                (4, 25190)
            else
              if b < 160 then
                (4, 25680)
              else
                if b < 161 then
                  (4, 25697)
                else
                  (4, 25701)
          else
            if b < 165 then
              if b < 163 then
                (4, 25940)
              else
                if b < 164 then
                  (4, 25941)
                else
                  (4, 26197)
            else
              if b < 166 then
                (5, 1537)
              else
                if b < 167 then
                  (5, 1558)
                else
                  (5, 1569)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (5, 1605)
              else
                if b < 170 then
                  (5, 1637)
                else
                  (5, 16737)
            else
              if b < 172 then
                (5, 24641)
              else
                if b < 173 then
                  (5, 24646)
                else
                  (5, 24933)
          else
            if b < 177 then
              if b < 175 then
                (5, 25108)
              else
                if b < 176 then
                  (5, 25172)
                else
                  (5, 25184)
            else
              if b < 178 then
                (5, 25876)
              else
                if b < 179 then
                  (5, 25893)
                else
                  (5, 411221)

def pointBlocks (_b : Nat) : Nat :=
  8182122233621725980452189460414623417445301916342059544257397654058515939906335411473906543841313909566491934079105424041257642979552744111162758429276840081027885478710642860134928971839793183885463197690281045847840500252801514220186681337519987690169177369853723824163664773347441289604583293732166757651188655907090598340262948149786461507764093671036750803268747345931572220745763945475387296732054971317563735384248157662970039550300052839784640942811709410365827922061447300526010723749245203133767879141640123675079080443411644157083669835518504166288445305352065180833122705517205592138229696719401086476856323536989281750267528051114404863534411630621229452290221425505754663872439359838160414202885899966858235324076656793854059131363260093243869431824192561145219755921087856661558404270482406277160

def point (r : Fin 180) : Fin 31671 :=
  Fin.ofNat 31671 ((pointBlocks (r.val / 256) >>> (15 * (r.val % 256))) % 32768)

def forward0Blocks (_b : Nat) : Nat :=
  20271851734667243677238554892034421739111730826874373068090502203495722577766235838659678245460630373230157503906886627572611047335196419804666540042752023125933400713765925567345587477070181711685525971102448917171222463072649169323811784152031837718883841034037835130797653915956656499652589247139899220599990937276796687394354318890427720000675741713345671014137861619531004632929006050588098072822165374309717366267409618914379265

def backward0Blocks (_b : Nat) : Nat :=
  19783459989683003885919460963384871364382982265282728543799445168357212184744338774758233926411628530450136932834308089489925981863215969696648228288525694713679564804857755882778035769004876315613753847398130410145069342210640701415000814270386541684237109741833647725128162515102044699734792798391115303457083812337971689739310903830073545822840365767721824375988335194134145073818171540274381620989019019127732277594892280541609990

def factorCode0 (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              (0, 0)
            else
              if b < 3 then
                (8, 1094780422)
              else
                (0, 0)
          else
            if b < 8 then
              if b < 6 then
                (0, 0)
              else
                if b < 7 then
                  (0, 0)
                else
                  (21, 9026605757628788226938742)
            else
              if b < 9 then
                (0, 0)
              else
                if b < 10 then
                  (0, 0)
                else
                  (16, 5135868584245010432)
        else
          if b < 16 then
            if b < 13 then
              (0, 0)
            else
              if b < 14 then
                (8, 1094780422)
              else
                if b < 15 then
                  (8, 1679036512)
                else
                  (17, 82308970157540066679)
          else
            if b < 19 then
              if b < 17 then
                (0, 0)
              else
                if b < 18 then
                  (0, 0)
                else
                  (8, 1094780422)
            else
              (0, 0)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (12, 75210267313670)
              else
                (18, 1557597568669676863494)
            else
              if b < 25 then
                (0, 0)
              else
                if b < 26 then
                  (18, 1557597568669676863494)
                else
                  (0, 0)
          else
            if b < 30 then
              if b < 28 then
                (8, 2002024276)
              else
                if b < 29 then
                  (0, 0)
                else
                  (8, 1679036512)
            else
              if b < 31 then
                (14, 19269222328701968)
              else
                if b < 32 then
                  (11, 2199833817651)
                else
                  (14, 10168287828844595)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (8, 1679036512)
              else
                if b < 35 then
                  (9, 17716941889)
                else
                  (12, 75888650825763)
            else
              if b < 37 then
                (0, 0)
              else
                if b < 38 then
                  (15, 163051196691656752)
                else
                  (0, 0)
          else
            if b < 42 then
              if b < 40 then
                (14, 33345250769716320)
              else
                (0, 0)
            else
              if b < 43 then
                (12, 39719862809088)
              else
                if b < 44 then
                  (1, 6)
                else
                  (11, 8205335032902)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                (18, 941950943150088667699)
              else
                (0, 0)
            else
              if b < 48 then
                (19, 20148993903402345889798)
              else
                if b < 49 then
                  (0, 0)
                else
                  (8, 1196700768)
          else
            if b < 53 then
              if b < 51 then
                (8, 658571312)
              else
                if b < 52 then
                  (0, 0)
                else
                  (15, 320938941579659014)
            else
              if b < 54 then
                (17, 115586854980615798790)
              else
                if b < 55 then
                  (0, 0)
                else
                  (11, 4898216572000)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (0, 0)
              else
                (12, 130049278153744)
            else
              if b < 59 then
                (0, 0)
              else
                if b < 60 then
                  (15, 307484222517420032)
                else
                  (14, 33572987405092358)
          else
            if b < 64 then
              if b < 62 then
                (0, 0)
              else
                if b < 63 then
                  (9, 21480555616)
                else
                  (7, 68423776)
            else
              if b < 65 then
                (0, 0)
              else
                if b < 66 then
                  (0, 0)
                else
                  (13, 1201178457227526)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (17, 100810109270818424582)
              else
                (17, 41741106340145926960)
            else
              if b < 70 then
                (19, 20167439240170442006528)
              else
                if b < 71 then
                  (9, 19130425344)
                else
                  (8, 1107763216)
          else
            if b < 75 then
              if b < 73 then
                (19, 20151286013313575747840)
              else
                if b < 74 then
                  (15, 432473606940214647)
                else
                  (12, 39719941460787)
            else
              if b < 76 then
                (19, 30479169233453794674039)
              else
                if b < 77 then
                  (0, 0)
                else
                  (10, 443578341238)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (10, 444349248838)
              else
                if b < 80 then
                  (9, 18593830726)
                else
                  (15, 229968491949597443)
            else
              if b < 82 then
                (15, 537410984610121222)
              else
                if b < 83 then
                  (18, 2166731673560284611959)
                else
                  (20, 563222062164534505899782)
          else
            if b < 87 then
              if b < 85 then
                (11, 4743037452338)
              else
                (15, 321011521926807814)
            else
              if b < 88 then
                (11, 4743037452338)
              else
                if b < 89 then
                  (14, 10168773277516544)
                else
                  (16, 8594635507542204416)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (13, 638838877913139)
              else
                (9, 26918339956)
            else
              if b < 93 then
                (5, 201776)
              else
                if b < 94 then
                  (17, 100305706038343106566)
                else
                  (11, 4703332340752)
          else
            if b < 98 then
              if b < 96 then
                (19, 34317862403411322015744)
              else
                if b < 97 then
                  (11, 6001215610880)
                else
                  (17, 41812954234369684528)
            else
              if b < 99 then
                (12, 75128714315590)
              else
                if b < 100 then
                  (19, 34317862403411322015744)
                else
                  (9, 32044680032)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (0, 0)
              else
                (11, 2495464362752)
            else
              if b < 104 then
                (6, 3359302)
              else
                if b < 105 then
                  (14, 10221403739861040)
                else
                  (15, 308290310085494278)
          else
            if b < 109 then
              if b < 107 then
                (17, 82308970157540066679)
              else
                (8, 1464291446)
            else
              if b < 110 then
                (12, 72580974252851)
              else
                if b < 111 then
                  (19, 19855844117395147001858)
                else
                  (19, 34667504220460513624096)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (17, 96000701300693073926)
              else
                (8, 2002208071)
            else
              if b < 115 then
                (8, 1144144736)
              else
                if b < 116 then
                  (20, 397939249587443168920951)
                else
                  (0, 0)
          else
            if b < 120 then
              if b < 118 then
                (4, 18192)
              else
                if b < 119 then
                  (10, 155966703426)
                else
                  (13, 638837787406336)
            else
              if b < 121 then
                (11, 7096432530448)
              else
                if b < 122 then
                  (10, 155966517808)
                else
                  (11, 7096432530448)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (15, 320449392297854327)
              else
                if b < 125 then
                  (9, 12901745440)
                else
                  (10, 306930193478)
            else
              if b < 127 then
                (10, 284613939203)
              else
                if b < 128 then
                  (13, 1532106210826102)
                else
                  (12, 72861168635953)
          else
            if b < 132 then
              if b < 130 then
                (11, 5997728317766)
              else
                if b < 131 then
                  (13, 1532106210826102)
                else
                  (17, 115378902221356029814)
            else
              if b < 133 then
                (18, 1262828888423187030128)
              else
                if b < 134 then
                  (11, 4703257706758)
                else
                  (5, 201472)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (0, 0)
              else
                (15, 303487493023598342)
            else
              if b < 138 then
                (8, 1947234630)
              else
                if b < 139 then
                  (20, 322381385280978133917808)
                else
                  (13, 1221855741559046)
          else
            if b < 143 then
              if b < 141 then
                (19, 35201315884155850133504)
              else
                if b < 142 then
                  (18, 671308377222734164017)
                else
                  (18, 669011771318334402595)
            else
              if b < 144 then
                (10, 293185007920)
              else
                if b < 145 then
                  (11, 4691833389361)
                else
                  (15, 524498332138554743)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (15, 162692881028481331)
              else
                (13, 638837738336304)
            else
              if b < 149 then
                (14, 10221403739915059)
              else
                if b < 150 then
                  (9, 32052107126)
                else
                  (10, 137760871218)
          else
            if b < 154 then
              if b < 152 then
                (14, 19268340803637248)
              else
                if b < 153 then
                  (15, 505870126642569216)
                else
                  (10, 137526190896)
            else
              if b < 155 then
                (11, 4695594727236)
              else
                if b < 156 then
                  (21, 5158434071585894958109442)
                else
                  (16, 4833545767903240304)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (10, 808534278)
              else
                (18, 2181851950752103268358)
            else
              if b < 160 then
                (21, 7590401045823399097733120)
              else
                if b < 161 then
                  (15, 163332951981957123)
                else
                  (11, 4742986413312)
          else
            if b < 165 then
              if b < 163 then
                (20, 331843402833397425849719)
              else
                if b < 164 then
                  (8, 1682130438)
                else
                  (11, 5804453741943)
            else
              if b < 166 then
                (15, 321011521926807814)
              else
                if b < 167 then
                  (11, 2230554989361)
                else
                  (11, 8071440450656)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (14, 28278701797164550)
              else
                if b < 170 then
                  (20, 317693505878527936888832)
                else
                  (9, 16790291)
            else
              if b < 172 then
                (14, 28240145236104208)
              else
                if b < 173 then
                  (17, 82033423756116313463)
                else
                  (19, 10704116283998669385728)
          else
            if b < 177 then
              if b < 175 then
                (7, 125191284)
              else
                if b < 176 then
                  (13, 619094605116721)
                else
                  (12, 131345593758816)
            else
              if b < 178 then
                (12, 77259604326263)
              else
                if b < 179 then
                  (17, 41956773576537621347)
                else
                  (12, 127848560017670)

def treeEdge0 (b : Nat) : Bool :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              true
            else
              if b < 3 then
                false
              else
                true
          else
            if b < 8 then
              if b < 6 then
                true
              else
                false
            else
              if b < 9 then
                true
              else
                if b < 10 then
                  true
                else
                  false
        else
          if b < 16 then
            if b < 13 then
              true
            else
              false
          else
            if b < 19 then
              if b < 17 then
                true
              else
                if b < 18 then
                  true
                else
                  false
            else
              if b < 20 then
                true
              else
                if b < 21 then
                  true
                else
                  false
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              false
            else
              if b < 25 then
                true
              else
                if b < 26 then
                  false
                else
                  true
          else
            if b < 30 then
              if b < 28 then
                false
              else
                if b < 29 then
                  true
                else
                  false
            else
              false
        else
          if b < 39 then
            if b < 36 then
              false
            else
              if b < 37 then
                true
              else
                if b < 38 then
                  false
                else
                  true
          else
            if b < 42 then
              if b < 40 then
                false
              else
                true
            else
              false
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                false
              else
                true
            else
              if b < 48 then
                false
              else
                if b < 49 then
                  true
                else
                  false
          else
            if b < 53 then
              if b < 51 then
                false
              else
                if b < 52 then
                  true
                else
                  false
            else
              if b < 54 then
                false
              else
                if b < 55 then
                  true
                else
                  false
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                true
              else
                false
            else
              false
          else
            if b < 64 then
              if b < 62 then
                true
              else
                false
            else
              if b < 65 then
                true
              else
                if b < 66 then
                  true
                else
                  false
      else
        if b < 78 then
          if b < 72 then
            false
          else
            if b < 75 then
              false
            else
              if b < 76 then
                false
              else
                if b < 77 then
                  true
                else
                  false
        else
          false
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          false
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                true
              else
                false
            else
              false
          else
            false
      else
        false
    else
      false

def forward1Blocks (_b : Nat) : Nat :=
  10760473656447703367503298431089407097864463165594712488267318380825547975580417679532164575477009725179313516241954403207163802355585634994476162148645433699866329617119234685838876511996084993691324644968800764828620495259523898714884761703919286429842195846801468762323724247010443415103172023671542770266645712608785688845923216868939777626665227964764982440976955441224793446785744023244277076940122430674575101957744137026469890

def backward1Blocks (_b : Nat) : Nat :=
  20257417856000035982146474398509189992373432059319629119824176903000510481182490428280814539105791022564766654283935267911845407740689240893397476192201603796553272560383028886364359931081798227863671785153107188383785975280751176715653603853767176212804234988563245154324643531919951844060647469346444886361152434592891852677615769151026325622382873184362484699316195352829117336287568469289211574246600449183322313678685567138660865

def factorCode1 (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              if b < 1 then
                (0, 0)
              else
                (8, 1679036512)
            else
              if b < 3 then
                (8, 1094780422)
              else
                if b < 4 then
                  (21, 9026605757628788226938742)
                else
                  (0, 0)
          else
            if b < 8 then
              if b < 6 then
                (9, 18593830726)
              else
                if b < 7 then
                  (8, 1094780422)
                else
                  (0, 0)
            else
              if b < 9 then
                (0, 0)
              else
                if b < 10 then
                  (0, 0)
                else
                  (8, 1679036512)
        else
          if b < 16 then
            if b < 13 then
              (0, 0)
            else
              if b < 14 then
                (15, 523673492273776134)
              else
                if b < 15 then
                  (16, 5135868584245010432)
                else
                  (0, 0)
          else
            if b < 19 then
              if b < 17 then
                (17, 78773641151519343991)
              else
                if b < 18 then
                  (7, 68423776)
                else
                  (8, 1094780422)
            else
              if b < 20 then
                (0, 0)
              else
                if b < 21 then
                  (10, 293185007920)
                else
                  (10, 306406977536)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (18, 667857701442398991409)
              else
                (15, 505870126642569216)
            else
              if b < 25 then
                (11, 4695594727236)
              else
                if b < 26 then
                  (12, 128941180679494)
                else
                  (17, 115671657087839445104)
          else
            if b < 30 then
              if b < 28 then
                (0, 0)
              else
                if b < 29 then
                  (0, 0)
                else
                  (21, 9026605757628788226938742)
            else
              if b < 31 then
                (13, 1535292284682502)
              else
                if b < 32 then
                  (14, 19427292479553587)
                else
                  (8, 1094780422)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (8, 1679036512)
              else
                if b < 35 then
                  (19, 34372369790758782439424)
                else
                  (19, 34317862403411322015744)
            else
              if b < 37 then
                (0, 0)
              else
                if b < 38 then
                  (0, 0)
                else
                  (17, 100305706038343106566)
          else
            if b < 42 then
              if b < 40 then
                (0, 0)
              else
                if b < 41 then
                  (15, 320938941579659014)
                else
                  (15, 235440917403797254)
            else
              if b < 43 then
                (8, 1679036512)
              else
                if b < 44 then
                  (1, 6)
                else
                  (13, 1820054488618000)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                (6, 4417286)
              else
                (19, 21056113221708701437952)
            else
              if b < 48 then
                (19, 20148993903402345889798)
              else
                if b < 49 then
                  (0, 0)
                else
                  (8, 1196700768)
          else
            if b < 53 then
              if b < 51 then
                (10, 155159118611)
              else
                (0, 0)
            else
              if b < 54 then
                (9, 1880101904)
              else
                if b < 55 then
                  (19, 21052726198403897360416)
                else
                  (9, 19062194182)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (0, 0)
              else
                (17, 79871470315726114816)
            else
              if b < 59 then
                (12, 128948968440928)
              else
                if b < 60 then
                  (7, 69690179)
                else
                  (8, 1094780422)
          else
            if b < 64 then
              if b < 62 then
                (13, 1819997883536400)
              else
                if b < 63 then
                  (1, 6)
                else
                  (7, 68423776)
            else
              if b < 65 then
                (19, 20739217117668842672915)
              else
                if b < 66 then
                  (18, 667857701442398991409)
                else
                  (13, 1201041450409984)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (10, 306406977536)
              else
                (0, 0)
            else
              if b < 70 then
                (14, 9905513676538656)
              else
                if b < 71 then
                  (15, 310841026212278576)
                else
                  (7, 37910277)
          else
            if b < 75 then
              if b < 73 then
                (13, 1201041450409984)
              else
                if b < 74 then
                  (15, 316455339320344835)
                else
                  (0, 0)
            else
              if b < 76 then
                (14, 9905513676538656)
              else
                if b < 77 then
                  (16, 7225256163291561990)
                else
                  (0, 0)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (20, 554716744843924324435319)
              else
                if b < 80 then
                  (17, 134060132543136663302)
                else
                  (16, 2608819146259116080)
            else
              if b < 82 then
                (19, 20797565732179486441990)
              else
                if b < 83 then
                  (18, 941950943013975175168)
                else
                  (14, 128853366276614)
          else
            if b < 87 then
              if b < 85 then
                (0, 0)
              else
                if b < 86 then
                  (10, 430695346500)
                else
                  (0, 0)
            else
              if b < 88 then
                (18, 1555603059254986491255)
              else
                if b < 89 then
                  (16, 4919747560278668035)
                else
                  (15, 524184778095989776)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (0, 0)
              else
                (9, 22619947014)
            else
              if b < 93 then
                (9, 31478543732)
              else
                if b < 94 then
                  (0, 0)
                else
                  (9, 18376578903)
          else
            if b < 98 then
              if b < 96 then
                (15, 523653695879118854)
              else
                if b < 97 then
                  (0, 0)
                else
                  (17, 82372882706912794486)
            else
              if b < 99 then
                (10, 362779276612)
              else
                if b < 100 then
                  (19, 34317862403411322015744)
                else
                  (13, 1535405511165446)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (12, 75888583716912)
              else
                (16, 8607633929983312134)
            else
              if b < 104 then
                (14, 10208309498937346)
              else
                (21, 8790520646684622994866182)
          else
            if b < 109 then
              if b < 107 then
                (0, 0)
              else
                if b < 108 then
                  (10, 362241528852)
                else
                  (20, 563571482894864211771910)
            else
              if b < 110 then
                (14, 23739861663424624)
              else
                if b < 111 then
                  (7, 36705296)
                else
                  (13, 1535280963405318)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (17, 81889234818281046022)
              else
                (11, 4910831060854)
            else
              if b < 115 then
                (13, 635548892934659)
              else
                if b < 116 then
                  (20, 397939249587443168920951)
                else
                  (19, 20148993903402345889798)
          else
            if b < 120 then
              if b < 118 then
                (15, 302976137045213488)
              else
                if b < 119 then
                  (16, 2535811501198214704)
                else
                  (18, 1259383318258238161202)
            else
              if b < 121 then
                (9, 9446634035)
              else
                if b < 122 then
                  (9, 825229331)
                else
                  (19, 21034075926976346408311)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (11, 8196214703622)
              else
                if b < 125 then
                  (9, 26961190912)
                else
                  (11, 7989816852512)
            else
              if b < 127 then
                (20, 549054977039271815759223)
              else
                if b < 128 then
                  (17, 136366029432070283264)
                else
                  (15, 308290241366004752)
          else
            if b < 132 then
              if b < 130 then
                (13, 1214222760416003)
              else
                if b < 131 then
                  (11, 4909490586720)
                else
                  (10, 1397960706)
            else
              if b < 133 then
                (14, 19217763906302256)
              else
                if b < 134 then
                  (17, 119277842127829550455)
                else
                  (13, 635518531601201)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (19, 35238200333492504625158)
              else
                (15, 316455339313607216)
            else
              if b < 138 then
                (9, 19164132470)
              else
                if b < 139 then
                  (15, 310836691751600643)
                else
                  (14, 10190699790087200)
          else
            if b < 143 then
              if b < 141 then
                (15, 393858556723544326)
              else
                if b < 142 then
                  (15, 163051196641210416)
                else
                  (17, 78715960963704554288)
            else
              if b < 144 then
                (15, 321241114003769094)
              else
                if b < 145 then
                  (18, 1314854470214421258240)
                else
                  (12, 75279087531104)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (19, 10740934035593550377760)
              else
                (18, 2200302370493184475168)
            else
              if b < 149 then
                (14, 29119828143980806)
              else
                if b < 150 then
                  (9, 32052107126)
                else
                  (11, 8187398930694)
          else
            if b < 154 then
              if b < 152 then
                (16, 4829869009592075639)
              else
                if b < 153 then
                  (21, 8785765076008315891220998)
                else
                  (13, 898314425008931)
            else
              if b < 155 then
                (9, 18327474208)
              else
                if b < 156 then
                  (18, 1259455375832721589024)
                else
                  (13, 2083881430238583)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (14, 18577361616306992)
              else
                (13, 2098367224287232)
            else
              if b < 160 then
                (14, 9905513676538656)
              else
                if b < 161 then
                  (15, 163332951981957123)
                else
                  (10, 210456740352)
          else
            if b < 165 then
              if b < 163 then
                (9, 23422308358)
              else
                if b < 164 then
                  (8, 1682130438)
                else
                  (8, 1465337206)
            else
              if b < 166 then
                (8, 1107755312)
              else
                if b < 167 then
                  (10, 306893498180)
                else
                  (19, 15071215090401182875696)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (15, 310839702792962816)
              else
                if b < 170 then
                  (18, 941950943150190248448)
                else
                  (3, 1814)
            else
              if b < 172 then
                (17, 100305706038343106566)
              else
                if b < 173 then
                  (12, 39927408505137)
                else
                  (19, 19855844117407996051459)
          else
            if b < 177 then
              if b < 175 then
                (16, 4923352704240189472)
              else
                if b < 176 then
                  (16, 3679495871771656979)
                else
                  (11, 4692105171984)
            else
              if b < 178 then
                (14, 19711238476007174)
              else
                if b < 179 then
                  (10, 283473281842)
                else
                  (3, 790)

def treeEdge1 (b : Nat) : Bool :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              if b < 1 then
                true
              else
                false
            else
              if b < 3 then
                false
              else
                if b < 4 then
                  false
                else
                  true
          else
            if b < 8 then
              if b < 6 then
                false
              else
                if b < 7 then
                  false
                else
                  true
            else
              if b < 9 then
                true
              else
                if b < 10 then
                  true
                else
                  false
        else
          if b < 16 then
            if b < 13 then
              true
            else
              if b < 14 then
                false
              else
                if b < 15 then
                  false
                else
                  true
          else
            if b < 19 then
              false
            else
              if b < 20 then
                true
              else
                false
      else
        if b < 33 then
          if b < 27 then
            false
          else
            if b < 30 then
              if b < 28 then
                true
              else
                if b < 29 then
                  true
                else
                  false
            else
              false
        else
          if b < 39 then
            if b < 36 then
              false
            else
              if b < 37 then
                true
              else
                if b < 38 then
                  true
                else
                  false
          else
            if b < 42 then
              if b < 40 then
                true
              else
                false
            else
              false
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              false
            else
              if b < 48 then
                false
              else
                if b < 49 then
                  true
                else
                  false
          else
            if b < 53 then
              if b < 51 then
                false
              else
                if b < 52 then
                  true
                else
                  false
            else
              false
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                true
              else
                false
            else
              false
          else
            false
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                false
              else
                true
            else
              false
          else
            if b < 75 then
              if b < 73 then
                false
              else
                if b < 74 then
                  false
                else
                  true
            else
              if b < 76 then
                false
              else
                if b < 77 then
                  false
                else
                  true
        else
          if b < 84 then
            false
          else
            if b < 87 then
              if b < 85 then
                true
              else
                if b < 86 then
                  false
                else
                  true
            else
              false
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                true
              else
                false
            else
              if b < 93 then
                false
              else
                if b < 94 then
                  true
                else
                  false
          else
            false
        else
          false
      else
        false
    else
      false

def forward2Blocks (_b : Nat) : Nat :=
  21337237914698726361936480320129677682450051894844247171363515799050541909432829144829806155393788675910922303038504700073487803241318009619232617326076777887802402277884728682273442797848457315088301126740092963971055680900367926520389254991407349855727229875321872197271805090621930661304829103112885162173679635742856984289048418599353354537079722734407756178859566250811666276361751873126998661881380873331260001753056638845125120

def backward2Blocks (_b : Nat) : Nat :=
  21337237914698726361936480320129677682450051894844247171363515799050541909432829144829806155393788675910922303038504700073487803241318009619232617326076777887802402277884728682273442797848457315088301126740092963971055680900367926520389254991407349855727229875321872197271805090621930661304829103112885162173679635742856984289048418599353354537079722734407756178859566250811666276361751873126998661881380873331260001753056638845125120

def factorCode2 (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              if b < 1 then
                (1, 6)
              else
                (9, 26864584198)
            else
              if b < 3 then
                (9, 26864584198)
              else
                if b < 4 then
                  (14, 32729593267111008)
                else
                  (0, 0)
          else
            if b < 8 then
              if b < 6 then
                (0, 0)
              else
                if b < 7 then
                  (7, 68423776)
                else
                  (14, 32729593267111008)
            else
              if b < 9 then
                (9, 26864584198)
              else
                if b < 10 then
                  (0, 0)
                else
                  (14, 32729593267111008)
        else
          if b < 16 then
            if b < 13 then
              if b < 12 then
                (9, 26864584198)
              else
                (12, 131126544057862)
            else
              if b < 14 then
                (14, 32729593267111008)
              else
                if b < 15 then
                  (9, 26864584198)
                else
                  (1, 6)
          else
            if b < 19 then
              if b < 17 then
                (0, 0)
              else
                (7, 68423776)
            else
              if b < 20 then
                (0, 0)
              else
                if b < 21 then
                  (13, 1201041450409984)
                else
                  (0, 0)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (11, 4700641707104)
              else
                (11, 4695594727236)
            else
              if b < 25 then
                (0, 0)
              else
                if b < 26 then
                  (14, 9905513676538656)
                else
                  (19, 20167439240170442006528)
          else
            if b < 30 then
              if b < 28 then
                (13, 898525503627376)
              else
                if b < 29 then
                  (0, 0)
                else
                  (14, 32729593267111008)
            else
              if b < 31 then
                (9, 26864584198)
              else
                if b < 32 then
                  (12, 78371363230736)
                else
                  (1, 6)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (1, 6)
              else
                if b < 35 then
                  (19, 35260106436852294557808)
                else
                  (19, 34317862403411322015744)
            else
              if b < 37 then
                (19, 34317862403411322015744)
              else
                if b < 38 then
                  (0, 0)
                else
                  (16, 8607633929983312134)
          else
            if b < 42 then
              if b < 40 then
                (0, 0)
              else
                if b < 41 then
                  (9, 26864584198)
                else
                  (21, 6367896130238520174598006)
            else
              if b < 43 then
                (8, 1679036512)
              else
                if b < 44 then
                  (8, 1679036512)
                else
                  (12, 131204628354064)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                (13, 1253951260607584)
              else
                (15, 505870126642569216)
            else
              if b < 48 then
                (15, 505870126642569216)
              else
                if b < 49 then
                  (14, 24616228516610310)
                else
                  (3, 871)
          else
            if b < 53 then
              if b < 51 then
                (0, 0)
              else
                if b < 52 then
                  (0, 0)
                else
                  (1, 6)
            else
              if b < 54 then
                (13, 1253951260607584)
              else
                if b < 55 then
                  (9, 19062194182)
                else
                  (0, 0)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (5, 30260)
              else
                (18, 1314795636446730592256)
            else
              if b < 59 then
                (11, 4535490720256)
              else
                if b < 60 then
                  (16, 8607618412313855494)
                else
                  (7, 68423776)
          else
            if b < 64 then
              if b < 62 then
                (11, 4910831064182)
              else
                (8, 1094780422)
            else
              if b < 65 then
                (13, 1201041450409984)
              else
                if b < 66 then
                  (19, 35260106436852294557808)
                else
                  (12, 75279087531104)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (0, 0)
              else
                (14, 10221416590934833)
            else
              if b < 70 then
                (12, 128941180679494)
              else
                if b < 71 then
                  (15, 505870126642569216)
                else
                  (16, 6287306637212585984)
          else
            if b < 75 then
              if b < 73 then
                (14, 19831222397327222)
              else
                if b < 74 then
                  (18, 671308377222989033472)
                else
                  (6, 345926)
            else
              if b < 76 then
                (15, 505870126642569216)
              else
                if b < 77 then
                  (19, 20151286013313575747840)
                else
                  (15, 321011522231994118)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (16, 4919747560011215152)
              else
                if b < 80 then
                  (11, 2405501510448)
                else
                  (12, 75887778398515)
            else
              if b < 82 then
                (13, 898525503627376)
              else
                if b < 83 then
                  (5, 292400)
                else
                  (13, 1202266325467398)
          else
            if b < 87 then
              if b < 85 then
                (11, 8071440450656)
              else
                if b < 86 then
                  (19, 15071215090401182875696)
                else
                  (0, 0)
            else
              if b < 88 then
                (18, 1296201069824207684403)
              else
                if b < 89 then
                  (11, 8071440450656)
                else
                  (9, 31481861888)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (16, 8607633929983312134)
              else
                (18, 1314854470214421258240)
            else
              if b < 93 then
                (9, 18342179910)
              else
                if b < 94 then
                  (16, 8607633929983312134)
                else
                  (19, 34317862403411322015744)
          else
            if b < 98 then
              if b < 96 then
                (15, 163051196691656752)
              else
                if b < 97 then
                  (0, 0)
                else
                  (16, 8607633929983312134)
            else
              if b < 99 then
                (6, 2109460)
              else
                if b < 100 then
                  (0, 0)
                else
                  (15, 451578502693786640)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (17, 78715960989425087251)
              else
                (16, 8607633929983312134)
            else
              if b < 104 then
                (16, 8607618412313855494)
              else
                if b < 105 then
                  (21, 8790520646684622994866182)
                else
                  (0, 0)
          else
            if b < 109 then
              if b < 107 then
                (1, 6)
              else
                if b < 108 then
                  (9, 26961190912)
                else
                  (13, 2045603925673056)
            else
              if b < 110 then
                (14, 23739861663424624)
              else
                if b < 111 then
                  (19, 34352743863276517138432)
                else
                  (16, 1382958248150237190)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (8, 1145390598)
              else
                (18, 2148344661344486887424)
            else
              if b < 115 then
                (19, 35233314188554988181366)
              else
                if b < 116 then
                  (17, 58871933946879607603)
                else
                  (21, 6367896130238520174598006)
          else
            if b < 120 then
              if b < 118 then
                (18, 1259383318259044459267)
              else
                if b < 119 then
                  (15, 505870126642569216)
                else
                  (16, 2613309639647844213)
            else
              if b < 121 then
                (21, 6367896130238520174598006)
              else
                if b < 122 then
                  (21, 6367896130238520174598006)
                else
                  (19, 21034075926976346408311)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (18, 2203554813849076105248)
              else
                if b < 125 then
                  (0, 0)
                else
                  (18, 1259519250588724363782)
            else
              if b < 127 then
                (3, 871)
              else
                if b < 128 then
                  (17, 137720433148552496503)
                else
                  (14, 18936008568484097)
          else
            if b < 132 then
              if b < 130 then
                (0, 0)
              else
                if b < 131 then
                  (13, 638837817618688)
                else
                  (10, 1397960706)
            else
              if b < 133 then
                (16, 8607633929983312134)
              else
                if b < 134 then
                  (18, 2203233278097487888390)
                else
                  (14, 10221405637714691)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (14, 32780865494925574)
              else
                (5, 65862)
            else
              if b < 138 then
                (9, 19164132470)
              else
                if b < 139 then
                  (7, 53622278)
                else
                  (5, 30260)
          else
            if b < 143 then
              if b < 141 then
                (13, 2098380452283488)
              else
                if b < 142 then
                  (11, 8003209592838)
                else
                  (13, 1819997883536400)
            else
              if b < 144 then
                (13, 1201041450409984)
              else
                if b < 145 then
                  (9, 22619947014)
                else
                  (13, 1201041450409984)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (13, 1253951260607584)
              else
                (16, 7225008636286930944)
            else
              if b < 149 then
                (17, 135428998126498947072)
              else
                if b < 150 then
                  (9, 8593277184)
                else
                  (11, 4695594727236)
          else
            if b < 154 then
              if b < 152 then
                (13, 1764103980074502)
              else
                if b < 153 then
                  (3, 871)
                else
                  (15, 310836357582819330)
            else
              if b < 155 then
                (13, 1214217638314802)
              else
                if b < 156 then
                  (16, 5140653865007521792)
                else
                  (13, 635519116849154)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (8, 1145390598)
              else
                (13, 1200968442529143)
            else
              if b < 160 then
                (9, 22619947014)
              else
                if b < 161 then
                  (11, 4910276293728)
                else
                  (18, 1296201069855397708082)
          else
            if b < 165 then
              if b < 163 then
                (5, 30260)
              else
                if b < 164 then
                  (7, 88561526)
                else
                  (18, 669007267749915018035)
            else
              if b < 166 then
                (11, 8071440450656)
              else
                if b < 167 then
                  (11, 8003209592838)
                else
                  (10, 430695346500)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (19, 20151286013580905808387)
              else
                if b < 170 then
                  (5, 292400)
                else
                  (16, 8607633929983312134)
            else
              if b < 172 then
                (16, 8607633929983312134)
              else
                if b < 173 then
                  (18, 1906071981310212177952)
                else
                  (13, 2045603925673056)
          else
            if b < 177 then
              if b < 175 then
                (9, 9398452784)
              else
                if b < 176 then
                  (22, 86246720371994631442028406)
                else
                  (20, 554664863376217016321399)
            else
              if b < 178 then
                (15, 316454238613012512)
              else
                if b < 179 then
                  (13, 1161093691158579)
                else
                  (19, 34374747694871347676535)

def treeEdge2 (b : Nat) : Bool :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              false
            else
              if b < 3 then
                false
              else
                if b < 4 then
                  false
                else
                  true
          else
            if b < 8 then
              if b < 6 then
                true
              else
                false
            else
              if b < 9 then
                false
              else
                if b < 10 then
                  true
                else
                  false
        else
          if b < 16 then
            false
          else
            if b < 19 then
              if b < 17 then
                true
              else
                false
            else
              if b < 20 then
                false
              else
                if b < 21 then
                  false
                else
                  true
      else
        if b < 33 then
          if b < 27 then
            false
          else
            if b < 30 then
              if b < 28 then
                false
              else
                if b < 29 then
                  true
                else
                  false
            else
              false
        else
          if b < 39 then
            false
          else
            if b < 42 then
              if b < 40 then
                true
              else
                false
            else
              false
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            false
          else
            if b < 53 then
              if b < 51 then
                true
              else
                if b < 52 then
                  true
                else
                  false
            else
              false
        else
          false
      else
        false
  else
    false

def forward3Blocks (_b : Nat) : Nat :=
  21337237914698726361936480320129677682450051894844247171363515799050541909432829144829806155393788675910922303038504700073487803241318009619232617326076777887802402277884728682273442797848457315088301126740092963971055680900367926520389254991407349855727229875321872197271805090621930661304829103112885162173679635742856984289048418599353354537079722734407756178859566250811666276361751873126998661881380873331260001753056638845125120

def backward3Blocks (_b : Nat) : Nat :=
  21337237914698726361936480320129677682450051894844247171363515799050541909432829144829806155393788675910922303038504700073487803241318009619232617326076777887802402277884728682273442797848457315088301126740092963971055680900367926520389254991407349855727229875321872197271805090621930661304829103112885162173679635742856984289048418599353354537079722734407756178859566250811666276361751873126998661881380873331260001753056638845125120

def factorCode3 (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            if b < 2 then
              if b < 1 then
                (1, 5)
              else
                (9, 22569616902)
            else
              if b < 3 then
                (9, 22569616902)
              else
                if b < 4 then
                  (14, 32729524547634272)
                else
                  (2, 86)
          else
            if b < 8 then
              if b < 6 then
                (2, 86)
              else
                if b < 7 then
                  (7, 69472352)
                else
                  (14, 32729524547634272)
            else
              if b < 9 then
                (9, 22569616902)
              else
                if b < 10 then
                  (2, 86)
                else
                  (14, 32729524547634272)
        else
          if b < 16 then
            if b < 13 then
              if b < 12 then
                (9, 22569616902)
              else
                (12, 131122249090566)
            else
              if b < 14 then
                (14, 32729524547634272)
              else
                if b < 15 then
                  (9, 22569616902)
                else
                  (1, 5)
          else
            if b < 19 then
              if b < 17 then
                (2, 86)
              else
                (7, 69472352)
            else
              if b < 20 then
                (2, 86)
              else
                if b < 21 then
                  (13, 1201110169886720)
                else
                  (2, 86)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (11, 4696346739808)
              else
                (11, 4699889694532)
            else
              if b < 25 then
                (2, 86)
              else
                if b < 26 then
                  (14, 9905513676538640)
                else
                  (19, 20185885984244151558144)
          else
            if b < 30 then
              if b < 28 then
                (13, 899625015255152)
              else
                if b < 29 then
                  (2, 86)
                else
                  (14, 32729524547634272)
            else
              if b < 31 then
                (9, 22569616902)
              else
                if b < 32 then
                  (12, 78371380007952)
                else
                  (1, 5)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (1, 5)
              else
                if b < 35 then
                  (19, 35260106155377317847152)
                else
                  (19, 34316709481906715168768)
            else
              if b < 37 then
                (19, 34316709481906715168768)
              else
                if b < 38 then
                  (2, 86)
                else
                  (16, 8607635029494939910)
          else
            if b < 42 then
              if b < 40 then
                (2, 86)
              else
                if b < 41 then
                  (9, 22569616902)
                else
                  (21, 7576821949853149349304182)
            else
              if b < 43 then
                (8, 1410601056)
              else
                if b < 44 then
                  (8, 1410601056)
                else
                  (12, 131273347830800)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                (13, 1253946965640288)
              else
                (15, 505869027130941440)
            else
              if b < 48 then
                (15, 505869027130941440)
              else
                if b < 49 then
                  (14, 29119828143980806)
                else
                  (3, 855)
          else
            if b < 53 then
              if b < 51 then
                (2, 86)
              else
                if b < 52 then
                  (2, 86)
                else
                  (1, 5)
            else
              if b < 54 then
                (13, 1253946965640288)
              else
                if b < 55 then
                  (11, 4905124364294)
                else
                  (2, 86)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (5, 30004)
              else
                (18, 1314723578852692664320)
            else
              if b < 59 then
                (11, 4535490720000)
              else
                if b < 60 then
                  (16, 8607600820127811078)
                else
                  (7, 69472352)
          else
            if b < 64 then
              if b < 62 then
                (11, 4910562628726)
              else
                (8, 1111557638)
            else
              if b < 65 then
                (13, 1201110169886720)
              else
                if b < 66 then
                  (19, 35260106155377317847152)
                else
                  (12, 75279087596640)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (2, 86)
              else
                (14, 10221416590934834)
            else
              if b < 70 then
                (12, 130040692307270)
              else
                if b < 71 then
                  (15, 505869027130941440)
                else
                  (16, 7440228141819432960)
          else
            if b < 75 then
              if b < 73 then
                (14, 19549747420616566)
              else
                if b < 74 then
                  (18, 671308377222989099008)
                else
                  (6, 411462)
            else
              if b < 76 then
                (15, 505869027130941440)
              else
                if b < 77 then
                  (19, 20151286013313575748096)
                else
                  (15, 321010422720366342)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (16, 4919747560011215408)
              else
                if b < 80 then
                  (11, 2405501506352)
                else
                  (12, 75887778398771)
            else
              if b < 82 then
                (13, 899625015255152)
              else
                if b < 83 then
                  (5, 292144)
                else
                  (13, 1203365837095174)
          else
            if b < 87 then
              if b < 85 then
                (11, 8140159927392)
              else
                if b < 86 then
                  (19, 15071215090401182810160)
                else
                  (2, 86)
            else
              if b < 88 then
                (18, 1296201069824224461619)
              else
                if b < 89 then
                  (11, 8140159927392)
                else
                  (9, 31750297344)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (16, 8607635029494939910)
              else
                (18, 1314854469114909630464)
            else
              if b < 93 then
                (9, 18358957126)
              else
                if b < 94 then
                  (16, 8607635029494939910)
                else
                  (19, 34316709481906715168768)
          else
            if b < 98 then
              if b < 96 then
                (15, 163051196691591216)
              else
                if b < 97 then
                  (2, 86)
                else
                  (16, 8607635029494939910)
            else
              if b < 99 then
                (6, 2109476)
              else
                if b < 100 then
                  (2, 86)
                else
                  (15, 379520908655858704)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (17, 78715960989425087267)
              else
                (16, 8607635029494939910)
            else
              if b < 104 then
                (16, 8607600820127811078)
              else
                if b < 105 then
                  (21, 8795243013167492640079878)
                else
                  (2, 86)
          else
            if b < 109 then
              if b < 107 then
                (1, 5)
              else
                if b < 108 then
                  (9, 22666223616)
                else
                  (13, 2045603926721632)
            else
              if b < 110 then
                (14, 28243461290795120)
              else
                if b < 111 then
                  (19, 34334297119202807586816)
                else
                  (16, 2535879752757084166)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (8, 1145127174)
              else
                (18, 2148272603750448959488)
            else
              if b < 115 then
                (19, 35214867444481278629750)
              else
                if b < 116 then
                  (17, 58871933946879673139)
                else
                  (21, 7576821949853149349304182)
          else
            if b < 120 then
              if b < 118 then
                (18, 1259383318259044455171)
              else
                if b < 119 then
                  (15, 505869027130941440)
                else
                  (16, 2613309639647844214)
            else
              if b < 121 then
                (21, 7576821949853149349304182)
              else
                if b < 122 then
                  (21, 7576821949853149349304182)
                else
                  (19, 21034003869382308480375)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (18, 2203554831441262149664)
              else
                if b < 125 then
                  (2, 86)
                else
                  (18, 1259523754188351734278)
            else
              if b < 127 then
                (3, 855)
              else
                if b < 128 then
                  (17, 137720714623529207159)
                else
                  (14, 18936008568484098)
          else
            if b < 132 then
              if b < 130 then
                (2, 86)
              else
                if b < 131 then
                  (13, 638837817618944)
                else
                  (10, 1397960705)
            else
              if b < 133 then
                (16, 8607635029494939910)
              else
                if b < 134 then
                  (16, 8606379107220062240)
                else
                  (14, 10221405637710595)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (14, 32779765983297798)
              else
                (5, 131398)
            else
              if b < 138 then
                (9, 19147355254)
              else
                if b < 139 then
                  (7, 53556742)
                else
                  (5, 30004)
          else
            if b < 143 then
              if b < 141 then
                (13, 2098380452217952)
              else
                if b < 142 then
                  (11, 8002941157382)
                else
                  (13, 1538522906825744)
            else
              if b < 144 then
                (13, 1201110169886720)
              else
                if b < 145 then
                  (9, 26914914310)
                else
                  (13, 1201110169886720)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (13, 1253946965640288)
              else
                (16, 6072087131680083968)
            else
              if b < 149 then
                (17, 136581919631105794048)
              else
                if b < 150 then
                  (9, 8593277440)
                else
                  (11, 4699889694532)
          else
            if b < 154 then
              if b < 152 then
                (13, 1482629003363846)
              else
                if b < 153 then
                  (3, 855)
                else
                  (15, 310836357582819329)
            else
              if b < 155 then
                (13, 1214217638314801)
              else
                if b < 156 then
                  (16, 5145157464634892288)
                else
                  (13, 635519116849153)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (8, 1145127174)
              else
                (13, 1200964147561847)
            else
              if b < 160 then
                (9, 26914914310)
              else
                if b < 161 then
                  (11, 4910276228192)
                else
                  (18, 1296201069855397708081)
          else
            if b < 165 then
              if b < 163 then
                (5, 30004)
              else
                if b < 164 then
                  (7, 105338742)
                else
                  (16, 5063285429122646835)
            else
              if b < 166 then
                (11, 8140159927392)
              else
                if b < 167 then
                  (11, 8002941157382)
                else
                  (10, 361975869764)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (19, 20151286013580905808131)
              else
                if b < 170 then
                  (5, 292144)
                else
                  (16, 8607635029494939910)
            else
              if b < 172 then
                (16, 8607635029494939910)
              else
                if b < 173 then
                  (18, 1610924076130859352096)
                else
                  (13, 2045603926721632)
          else
            if b < 177 then
              if b < 175 then
                (9, 9398452528)
              else
                if b < 176 then
                  (22, 86322278235720545765447542)
                else
                  (20, 559387229859086661535095)
            else
              if b < 178 then
                (15, 311950638985642016)
              else
                if b < 179 then
                  (13, 1161089396191283)
                else
                  (19, 34374819752465385604471)

def treeEdge3 (_b : Nat) : Bool :=
  false

def forward4Blocks (_b : Nat) : Nat :=
  10752698113307122716811203278582369341059216005806390021360286245248313319143739565523038209959862479412868544218253809549874208598660609324452378754236759297145035387472101426390342751440934219816899693977099518160475247745159152383874441788163999775428201939603199159680960850154653237477957686664649983866553728513905497371943061797985761695681615048835136918982284913161968217799562361443220194532361310251241040848087133968795395

def backward4Blocks (_b : Nat) : Nat :=
  20280100829127401197341536730355740526432877490022344688431254227474045679726178001187859644396268231431251870919043011166728116873876022976393527723257359838602721667789248397579683198946514438471883492349817257730072800005405504708345622282830636823934634360902390930548490508702196708697870668452989650149591711817406650921926735707331430917656662051799005279526443084271379532490534489366407910071913154532857990132441591548085770

def factorCode4 (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            (0, 0)
          else
            if b < 8 then
              if b < 6 then
                (0, 0)
              else
                if b < 7 then
                  (15, 523673492273776134)
                else
                  (8, 1679036512)
            else
              if b < 9 then
                (18, 1318101229305976014199)
              else
                if b < 10 then
                  (0, 0)
                else
                  (21, 9026605757628788226938742)
        else
          if b < 16 then
            if b < 13 then
              if b < 12 then
                (10, 297549644896)
              else
                (17, 58871933946879620656)
            else
              if b < 14 then
                (0, 0)
              else
                if b < 15 then
                  (21, 9026605757628788226938742)
                else
                  (17, 81012566864281403408)
          else
            if b < 19 then
              if b < 17 then
                (7, 74806359)
              else
                if b < 18 then
                  (14, 20095187077433094)
                else
                  (18, 1296411927305371385888)
            else
              if b < 20 then
                (0, 0)
              else
                if b < 21 then
                  (14, 33573675353587974)
                else
                  (13, 1183500538675760)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (17, 82385569834130153584)
              else
                (0, 0)
            else
              if b < 25 then
                (19, 20151286013313575747840)
              else
                if b < 26 then
                  (0, 0)
                else
                  (12, 128936332052342)
          else
            if b < 30 then
              if b < 28 then
                (19, 34319538925675294491142)
              else
                if b < 29 then
                  (0, 0)
                else
                  (16, 5135868584245010432)
            else
              if b < 31 then
                (11, 2482494320656)
              else
                if b < 32 then
                  (19, 10740934035564286648368)
                else
                  (17, 134276074422868844544)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (15, 310836541394071553)
              else
                if b < 35 then
                  (17, 82385569842702271863)
                else
                  (0, 0)
            else
              if b < 37 then
                (0, 0)
              else
                if b < 38 then
                  (18, 2148214599142604800518)
                else
                  (12, 53889226375174)
          else
            if b < 42 then
              if b < 40 then
                (13, 638838555869968)
              else
                if b < 41 then
                  (11, 4742993438464)
                else
                  (0, 0)
            else
              if b < 43 then
                (0, 0)
              else
                if b < 44 then
                  (19, 15071215090694042431744)
                else
                  (10, 499398218768)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                (13, 635530622538515)
              else
                (17, 134276076634226425888)
            else
              if b < 48 then
                (13, 1201148590560272)
              else
                if b < 49 then
                  (0, 0)
                else
                  (16, 4919747561960981554)
          else
            if b < 53 then
              if b < 51 then
                (0, 0)
              else
                if b < 52 then
                  (0, 0)
                else
                  (10, 302601672516)
            else
              if b < 54 then
                (0, 0)
              else
                if b < 55 then
                  (10, 306926678016)
                else
                  (15, 163542669497413680)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (0, 0)
              else
                (20, 166186942542242660954163)
            else
              if b < 59 then
                (13, 1201041450409984)
              else
                if b < 60 then
                  (10, 430645277815)
                else
                  (0, 0)
          else
            if b < 64 then
              if b < 62 then
                (16, 8584779270562455552)
              else
                if b < 63 then
                  (11, 4910832776262)
                else
                  (0, 0)
            else
              if b < 65 then
                (14, 20095187077433094)
              else
                if b < 66 then
                  (11, 8127220482144)
                else
                  (0, 0)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (11, 4902511640582)
              else
                (13, 1482352180068870)
            else
              if b < 70 then
                (19, 24892819426150915196279)
              else
                (0, 0)
          else
            if b < 75 then
              if b < 73 then
                (17, 81228071062616875120)
              else
                if b < 74 then
                  (16, 7225022929938092032)
                else
                  (13, 635519063359539)
            else
              if b < 76 then
                (9, 26966512724)
              else
                if b < 77 then
                  (13, 870006902965623)
                else
                  (19, 29597172354936008557943)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (8, 1951876183)
              else
                if b < 80 then
                  (0, 0)
                else
                  (19, 20204329969785280681846)
            else
              if b < 82 then
                (19, 10685723223077305910048)
              else
                if b < 83 then
                  (10, 513102272326)
                else
                  (17, 41812954234368299024)
          else
            if b < 87 then
              if b < 85 then
                (15, 229968491980198724)
              else
                if b < 86 then
                  (9, 10502996480)
                else
                  (17, 78616805502643015680)
            else
              if b < 88 then
                (10, 155966273091)
              else
                if b < 89 then
                  (15, 510877302044885024)
                else
                  (18, 1318097291748696334448)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (10, 280300098576)
              else
                (11, 2213303812131)
            else
              if b < 93 then
                (14, 10221416624619536)
              else
                if b < 94 then
                  (19, 35223226128559329723767)
                else
                  (9, 18327487523)
          else
            if b < 98 then
              if b < 96 then
                (10, 293187101488)
              else
                if b < 97 then
                  (13, 1214217906761728)
                else
                  (17, 100305706038343106566)
            else
              if b < 99 then
                (8, 606089473)
              else
                (0, 0)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (9, 32015204660)
              else
                (12, 75888650825763)
            else
              if b < 104 then
                (14, 33063720196510736)
              else
                if b < 105 then
                  (0, 0)
                else
                  (12, 75888923271216)
          else
            if b < 109 then
              if b < 107 then
                (11, 4535537041666)
              else
                if b < 108 then
                  (12, 75059191432288)
                else
                  (17, 78863790118470632823)
            else
              if b < 110 then
                (16, 7428406329685966880)
              else
                if b < 111 then
                  (9, 1998860320)
                else
                  (16, 6289088262986745207)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (11, 4536310891266)
              else
                (16, 5136203921584374022)
            else
              if b < 115 then
                (16, 3760858851401859078)
              else
                if b < 116 then
                  (19, 21089751039781853484918)
                else
                  (9, 13223592755)
          else
            if b < 120 then
              if b < 118 then
                (9, 9697432596)
              else
                if b < 119 then
                  (11, 4535572521011)
                else
                  (15, 163331852477990519)
            else
              if b < 121 then
                (17, 81871219183371620352)
              else
                if b < 122 then
                  (9, 17787015955)
                else
                  (10, 155159110400)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (18, 1853064968829507994118)
              else
                if b < 125 then
                  (11, 6885155816966)
                else
                  (8, 121844832)
            else
              if b < 127 then
                (12, 127987630740496)
              else
                if b < 128 then
                  (6, 476726)
                else
                  (20, 337433919156450896584816)
          else
            if b < 132 then
              if b < 130 then
                (13, 2098359004566544)
              else
                if b < 131 then
                  (10, 306893316150)
                else
                  (21, 6599290501787565100761094)
            else
              if b < 133 then
                (9, 26916165376)
              else
                if b < 134 then
                  (20, 564161909591087087878662)
                else
                  (19, 20502719617525111525376)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (14, 19427477934846256)
              else
                (13, 1214218413092880)
            else
              if b < 138 then
                (16, 8603924178123491078)
              else
                if b < 139 then
                  (10, 481627816198)
                else
                  (9, 8673846064)
          else
            if b < 143 then
              if b < 141 then
                (7, 52643334)
              else
                if b < 142 then
                  (14, 19198792398217216)
                else
                  (20, 397996876816961730904070)
            else
              if b < 144 then
                (19, 20739217117668842672915)
              else
                if b < 145 then
                  (16, 4932128195180184951)
                else
                  (9, 21480555616)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (18, 1261531495406019543558)
              else
                (16, 5063285427141607987)
            else
              if b < 149 then
                (18, 1314625241835859559799)
              else
                if b < 150 then
                  (15, 310836545723772944)
                else
                  (17, 80999209842410389536)
          else
            if b < 154 then
              if b < 152 then
                (8, 805450496)
              else
                if b < 153 then
                  (19, 34374675633904884514848)
                else
                  (10, 513051817076)
            else
              if b < 155 then
                (20, 564109969292988703252480)
              else
                if b < 156 then
                  (11, 4679220348422)
                else
                  (18, 669011771348147569411)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (18, 941950943502259126291)
              else
                (16, 4919747560229311267)
            else
              if b < 160 then
                (12, 38693412820803)
              else
                if b < 161 then
                  (12, 72568659968560)
                else
                  (17, 58871933938340081667)
          else
            if b < 165 then
              if b < 163 then
                (12, 131135106794592)
              else
                if b < 164 then
                  (8, 588264193)
                else
                  (13, 1201178996577296)
            else
              if b < 166 then
                (11, 4910276293728)
              else
                if b < 167 then
                  (14, 19217763910746144)
                else
                  (10, 810549553)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (16, 8246372612007133216)
              else
                if b < 170 then
                  (11, 7848052868471)
                else
                  (7, 51393027)
            else
              if b < 172 then
                (11, 4553794855731)
              else
                if b < 173 then
                  (13, 636918737096705)
                else
                  (18, 2181635776875968202502)
          else
            if b < 177 then
              if b < 175 then
                (15, 163051196694667267)
              else
                if b < 176 then
                  (14, 33342983583645958)
                else
                  (14, 14373030749038336)
            else
              if b < 178 then
                (7, 71595862)
              else
                if b < 179 then
                  (9, 18324205600)
                else
                  (13, 2101464973919328)

def treeEdge4 (b : Nat) : Bool :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            true
          else
            if b < 8 then
              if b < 6 then
                true
              else
                false
            else
              if b < 9 then
                false
              else
                if b < 10 then
                  true
                else
                  false
        else
          if b < 16 then
            false
          else
            if b < 19 then
              false
            else
              if b < 20 then
                true
              else
                false
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                false
              else
                true
            else
              if b < 25 then
                false
              else
                if b < 26 then
                  true
                else
                  false
          else
            if b < 30 then
              if b < 28 then
                false
              else
                if b < 29 then
                  true
                else
                  false
            else
              false
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                false
              else
                if b < 35 then
                  false
                else
                  true
            else
              if b < 37 then
                true
              else
                false
          else
            if b < 42 then
              if b < 40 then
                false
              else
                if b < 41 then
                  false
                else
                  true
            else
              if b < 43 then
                true
              else
                false
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              false
            else
              if b < 48 then
                false
              else
                if b < 49 then
                  true
                else
                  false
          else
            if b < 53 then
              if b < 51 then
                true
              else
                if b < 52 then
                  true
                else
                  false
            else
              if b < 54 then
                true
              else
                false
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                true
              else
                false
            else
              if b < 59 then
                false
              else
                if b < 60 then
                  false
                else
                  true
          else
            if b < 64 then
              if b < 62 then
                false
              else
                if b < 63 then
                  false
                else
                  true
            else
              false
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              false
            else
              if b < 70 then
                false
              else
                true
          else
            false
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                false
              else
                if b < 80 then
                  true
                else
                  false
            else
              false
          else
            false
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            false
          else
            if b < 98 then
              false
            else
              if b < 99 then
                false
              else
                true
        else
          if b < 106 then
            if b < 103 then
              false
            else
              if b < 104 then
                false
              else
                if b < 105 then
                  true
                else
                  false
          else
            false
      else
        false
    else
      false

def forward5Blocks (_b : Nat) : Nat :=
  11833911840539715290856827411761933935472232868767287169651916651472531275430525297782908125756811027207064145104189044740307414715432096779416243708562869500200613451776740087918617698337322255361884036273006708239633489824242167343172439207273147555357991671981156742242509506578633364747142244162666930327355467815743761471223623922163448134663086325308659892720676979798558794643827304126974476352609409903709378172288569455609860

def backward5Blocks (_b : Nat) : Nat :=
  19181879603619491460012226607430751554363155276420455200029540844484408651850614419184081237625974792266288298091141890152691738369393013056388985921288728214464976783827147670764460152507350048996839499296945901322772462869915924762970227661048216883158936594480024876963889345922855415972710868002877237304738471686994477354730575429722113501156775224490717163938651781339715192984858211891535320517347735899352476827640135550128160

def factorCode5 (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            (0, 0)
          else
            if b < 8 then
              if b < 6 then
                (0, 0)
              else
                if b < 7 then
                  (9, 26864584198)
                else
                  (0, 0)
            else
              if b < 9 then
                (11, 7096484840566)
              else
                (0, 0)
        else
          if b < 16 then
            if b < 13 then
              (0, 0)
            else
              if b < 14 then
                (9, 17786994945)
              else
                if b < 15 then
                  (14, 10208240779884288)
                else
                  (9, 271586099)
          else
            if b < 19 then
              if b < 17 then
                (0, 0)
              else
                if b < 18 then
                  (11, 4743037456400)
                else
                  (0, 0)
            else
              if b < 20 then
                (17, 78715960989441916947)
              else
                if b < 21 then
                  (13, 638019343709238)
                else
                  (11, 8002719794806)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (13, 1214222758653987)
              else
                (0, 0)
            else
              (0, 0)
          else
            if b < 30 then
              if b < 28 then
                (0, 0)
              else
                if b < 29 then
                  (0, 0)
                else
                  (14, 19217763906097971)
            else
              if b < 31 then
                (19, 34374667453612583683846)
              else
                if b < 32 then
                  (16, 3634761571734148982)
                else
                  (17, 135199597119991390208)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (15, 163051196696953136)
              else
                if b < 35 then
                  (11, 8195943960576)
                else
                  (0, 0)
            else
              if b < 37 then
                (12, 7709738008582)
              else
                if b < 38 then
                  (0, 0)
                else
                  (20, 473514315336518800113696)
          else
            if b < 42 then
              if b < 40 then
                (21, 5083096094053501228810755)
              else
                if b < 41 then
                  (16, 3683948004229775878)
                else
                  (0, 0)
            else
              if b < 43 then
                (16, 8377899298733629440)
              else
                if b < 44 then
                  (10, 155159041090)
                else
                  (13, 1236363520327942)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                (0, 0)
              else
                (10, 500169987191)
            else
              if b < 48 then
                (0, 0)
              else
                if b < 49 then
                  (13, 640209557668624)
                else
                  (0, 0)
          else
            if b < 53 then
              if b < 51 then
                (14, 10221403705979136)
              else
                if b < 52 then
                  (0, 0)
                else
                  (9, 8623686451)
            else
              if b < 54 then
                (0, 0)
              else
                if b < 55 then
                  (19, 10704116283999431966977)
                else
                  (14, 10168283852443650)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (17, 40572984020474802483)
              else
                (16, 2613327231833014371)
            else
              if b < 59 then
                (7, 68423776)
              else
                if b < 60 then
                  (13, 2099471370896480)
                else
                  (11, 8002719794806)
          else
            if b < 64 then
              if b < 62 then
                (18, 941950943025534349571)
              else
                if b < 63 then
                  (13, 2098311712818272)
                else
                  (14, 29119964506046726)
            else
              if b < 65 then
                (11, 8209367646534)
              else
                if b < 66 then
                  (10, 293256382278)
                else
                  (8, 1416918343)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (8, 1094780422)
              else
                (8, 1128543328)
            else
              if b < 70 then
                (0, 0)
              else
                if b < 71 then
                  (0, 0)
                else
                  (13, 2045591794369632)
          else
            if b < 75 then
              if b < 73 then
                (14, 19268340803637248)
              else
                (0, 0)
            else
              if b < 76 then
                (10, 293239533873)
              else
                if b < 77 then
                  (17, 78715960989506036480)
                else
                  (0, 0)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (12, 77259604247312)
              else
                if b < 80 then
                  (0, 0)
                else
                  (12, 75887778398515)
            else
              if b < 82 then
                (18, 2202604461900004720646)
              else
                if b < 83 then
                  (0, 0)
                else
                  (14, 19427477966291249)
          else
            if b < 87 then
              if b < 85 then
                (14, 18577353564422194)
              else
                if b < 86 then
                  (16, 4847618192730882355)
                else
                  (14, 33573962364567814)
            else
              if b < 88 then
                (0, 0)
              else
                if b < 89 then
                  (18, 1552050491816807498246)
                else
                  (0, 0)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (10, 503659709812)
              else
                (11, 4759985853456)
            else
              if b < 93 then
                (9, 12901683200)
              else
                if b < 94 then
                  (11, 4553823158529)
                else
                  (16, 226096093869441030)
          else
            if b < 98 then
              if b < 96 then
                (14, 10221403739861040)
              else
                if b < 97 then
                  (8, 1413772384)
                else
                  (13, 1257104521577990)
            else
              if b < 99 then
                (0, 0)
              else
                if b < 100 then
                  (14, 10221403739861040)
                else
                  (20, 322970298993052189065222)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (13, 636918736901186)
              else
                (13, 1204246406239248)
            else
              if b < 104 then
                (19, 15071215088203470995507)
              else
                if b < 105 then
                  (10, 375075718980)
                else
                  (0, 0)
          else
            if b < 109 then
              if b < 107 then
                (13, 1257043636863238)
              else
                if b < 108 then
                  (20, 322974058710465114480752)
                else
                  (9, 25861506566)
            else
              if b < 110 then
                (16, 2608819146259369984)
              else
                if b < 111 then
                  (22, 144335720576951483832992262)
                else
                  (17, 58871933948025385729)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (14, 10221404511277874)
              else
                (8, 1198604550)
            else
              if b < 115 then
                (18, 1277974157436758524422)
              else
                if b < 116 then
                  (17, 134050861460789600368)
                else
                  (14, 20059792735290464)
          else
            if b < 120 then
              if b < 118 then
                (18, 669011771318381654800)
              else
                if b < 119 then
                  (10, 283587407875)
                else
                  (15, 229968491946799216)
            else
              if b < 121 then
                (13, 1203171000325136)
              else
                if b < 122 then
                  (10, 150914216704)
                else
                  (9, 32032179574)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (18, 1299870710502080381446)
              else
                if b < 125 then
                  (9, 31172079875)
                else
                  (20, 563276479390828675407984)
            else
              if b < 127 then
                (11, 2221359169537)
              else
                if b < 128 then
                  (20, 171854944569496738005507)
                else
                  (10, 293239795712)
          else
            if b < 132 then
              if b < 130 then
                (18, 941950943150120042754)
              else
                if b < 131 then
                  (21, 5172897385716512277528608)
                else
                  (17, 78922245571681058848)
            else
              if b < 133 then
                (10, 306141484116)
              else
                if b < 134 then
                  (7, 121718278)
                else
                  (11, 8177651291152)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (10, 305285842016)
              else
                (12, 131135039342086)
            else
              if b < 138 then
                (16, 3679495871144333344)
              else
                if b < 139 then
                  (13, 1214205242978611)
                else
                  (15, 163542670286783282)
          else
            if b < 143 then
              if b < 141 then
                (13, 2098380452283488)
              else
                if b < 142 then
                  (20, 166186942542522689270016)
                else
                  (11, 6890541307718)
            else
              if b < 144 then
                (14, 10168284879127347)
              else
                if b < 145 then
                  (16, 7441201415217872902)
                else
                  (15, 379557208967615504)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (14, 29087887042828150)
              else
                (20, 336569210010436172535670)
            else
              if b < 149 then
                (15, 163051196696761123)
              else
                if b < 150 then
                  (18, 1295969678522392724855)
                else
                  (10, 156531437825)
          else
            if b < 154 then
              if b < 152 then
                (13, 1161295588167715)
              else
                if b < 153 then
                  (11, 4695598061380)
                else
                  (13, 636918737088816)
            else
              if b < 155 then
                (7, 88561526)
              else
                if b < 156 then
                  (15, 537130423336247296)
                else
                  (15, 157960457807855648)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (11, 6878142940678)
              else
                (10, 482451146246)
            else
              if b < 160 then
                (16, 8382043555970359408)
              else
                if b < 161 then
                  (16, 7441200384425721888)
                else
                  (0, 0)
          else
            if b < 165 then
              if b < 163 then
                (12, 78427566994528)
              else
                if b < 164 then
                  (9, 17717086064)
                else
                  (13, 1214205259678514)
            else
              if b < 166 then
                (15, 307466630434150260)
              else
                if b < 167 then
                  (13, 1256141691581536)
                else
                  (18, 1296258488332582339959)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (13, 2066343502567286)
              else
                if b < 170 then
                  (7, 71763462)
                else
                  (12, 113748792775696)
            else
              if b < 172 then
                (17, 41812954234365179651)
              else
                if b < 173 then
                  (8, 117928451)
                else
                  (17, 136352517318928175104)
          else
            if b < 177 then
              if b < 175 then
                (11, 7990053914118)
              else
                if b < 176 then
                  (13, 1817992940176759)
                else
                  (15, 144449658925744134)
            else
              if b < 178 then
                (9, 32018613878)
              else
                if b < 179 then
                  (17, 41956773576488194865)
                else
                  (11, 4742986413312)

def treeEdge5 (b : Nat) : Bool :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            true
          else
            if b < 8 then
              if b < 6 then
                true
              else
                if b < 7 then
                  false
                else
                  true
            else
              if b < 9 then
                false
              else
                true
        else
          if b < 16 then
            if b < 13 then
              true
            else
              false
          else
            if b < 19 then
              if b < 17 then
                true
              else
                if b < 18 then
                  false
                else
                  true
            else
              false
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                false
              else
                true
            else
              true
          else
            if b < 30 then
              if b < 28 then
                true
              else
                if b < 29 then
                  true
                else
                  false
            else
              false
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                false
              else
                if b < 35 then
                  false
                else
                  true
            else
              if b < 37 then
                false
              else
                if b < 38 then
                  true
                else
                  false
          else
            if b < 42 then
              if b < 40 then
                false
              else
                if b < 41 then
                  false
                else
                  true
            else
              false
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              if b < 46 then
                true
              else
                false
            else
              if b < 48 then
                true
              else
                if b < 49 then
                  false
                else
                  true
          else
            if b < 53 then
              if b < 51 then
                false
              else
                if b < 52 then
                  true
                else
                  false
            else
              if b < 54 then
                true
              else
                false
        else
          false
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              false
            else
              if b < 70 then
                true
              else
                if b < 71 then
                  true
                else
                  false
          else
            if b < 75 then
              if b < 73 then
                false
              else
                true
            else
              if b < 76 then
                false
              else
                if b < 77 then
                  false
                else
                  true
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                false
              else
                if b < 80 then
                  true
                else
                  false
            else
              if b < 82 then
                false
              else
                if b < 83 then
                  true
                else
                  false
          else
            if b < 87 then
              false
            else
              if b < 88 then
                true
              else
                if b < 89 then
                  false
                else
                  true
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            false
          else
            if b < 98 then
              false
            else
              if b < 99 then
                true
              else
                false
        else
          if b < 106 then
            if b < 103 then
              false
            else
              if b < 104 then
                false
              else
                if b < 105 then
                  false
                else
                  true
          else
            false
      else
        false
    else
      if b < 157 then
        false
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              false
            else
              if b < 160 then
                false
              else
                if b < 161 then
                  false
                else
                  true
          else
            false
        else
          false

def forward6Blocks (_b : Nat) : Nat :=
  10516024215008458092606478345131240238830097616062358573448232171672365665217683584908488731776439138105389105381712442995445012464880086365726828899289125970098616999862504296842878641195449794479400292640986518521978633107365493875520919107212374918440711132914404649282308192309069428875461386340473107699584968179441501952092943199252807775525505001975773154036258469926592651990834766251282905810641138047612049802005182860232965

def backward6Blocks (_b : Nat) : Nat :=
  20608334826126218548570201564972869923049957481586454654400735136447353669245197845444360879277362470248968281355585161998863712217803099762516156786610930839776264982335426282771149333608409546176161253561046994957253248336716897517997045443851173748564174784403875286297673520579969197174914423406995487421010790134266346727813581028425798104231409243773378061884503576900892823370445965569847112025137394959771689634159767112130640

def factorCode6 (b : Nat) : Nat × Nat :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            (0, 0)
          else
            if b < 8 then
              (0, 0)
            else
              if b < 9 then
                (0, 0)
              else
                if b < 10 then
                  (11, 4743057585410)
                else
                  (0, 0)
        else
          if b < 16 then
            (0, 0)
          else
            if b < 19 then
              (0, 0)
            else
              if b < 20 then
                (0, 0)
              else
                if b < 21 then
                  (9, 26918274563)
                else
                  (0, 0)
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                (13, 2098147362083856)
              else
                (0, 0)
            else
              (0, 0)
          else
            if b < 30 then
              (0, 0)
            else
              if b < 31 then
                (9, 9697240832)
              else
                if b < 32 then
                  (14, 19427477126460161)
                else
                  (16, 2535811501193712724)
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                (0, 0)
              else
                if b < 35 then
                  (0, 0)
                else
                  (18, 1280897330128214054774)
            else
              (0, 0)
          else
            if b < 42 then
              if b < 40 then
                (14, 19271571748439558)
              else
                if b < 41 then
                  (16, 7225820491929485318)
                else
                  (0, 0)
            else
              if b < 43 then
                (0, 0)
              else
                if b < 44 then
                  (0, 0)
                else
                  (16, 3679495871197688371)
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              (0, 0)
            else
              if b < 48 then
                (0, 0)
              else
                if b < 49 then
                  (17, 100625412207787923318)
                else
                  (18, 2181649238191887294464)
          else
            if b < 53 then
              if b < 51 then
                (0, 0)
              else
                if b < 52 then
                  (17, 41741106340149948448)
                else
                  (12, 92665386660960)
            else
              (0, 0)
        else
          if b < 61 then
            if b < 58 then
              if b < 57 then
                (13, 638015048742258)
              else
                (15, 163332951989748528)
            else
              if b < 59 then
                (17, 100611637731913834496)
              else
                if b < 60 then
                  (17, 58871933939114640147)
                else
                  (19, 20739217117669379997955)
          else
            if b < 64 then
              if b < 62 then
                (18, 1296201069854257590577)
              else
                if b < 63 then
                  (17, 136076667443705221120)
                else
                  (0, 0)
            else
              if b < 65 then
                (17, 119067089521103540224)
              else
                if b < 66 then
                  (14, 19217763910365187)
                else
                  (0, 0)
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                (0, 0)
              else
                (12, 110313084109062)
            else
              if b < 70 then
                (12, 35253900222467)
              else
                if b < 71 then
                  (15, 319884518199084407)
                else
                  (12, 39738195251248)
          else
            if b < 75 then
              if b < 73 then
                (14, 10168305064088370)
              else
                (0, 0)
            else
              if b < 76 then
                (10, 211309101826)
              else
                if b < 77 then
                  (19, 10685723223076535022355)
                else
                  (17, 134191353752863244320)
        else
          if b < 84 then
            if b < 81 then
              if b < 79 then
                (11, 7097287013472)
              else
                if b < 80 then
                  (19, 21074558784155663226742)
                else
                  (13, 1214204454376240)
            else
              if b < 82 then
                (13, 1201041525133415)
              else
                if b < 83 then
                  (14, 20098270562096144)
                else
                  (11, 6009785418246)
          else
            if b < 87 then
              if b < 85 then
                (12, 72599027847169)
              else
                if b < 86 then
                  (0, 0)
                else
                  (16, 465124498399692550)
            else
              if b < 88 then
                (14, 19778458699891505)
              else
                if b < 89 then
                  (15, 162695916679070000)
                else
                  (10, 306926929268)
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              if b < 91 then
                (14, 19217763906236464)
              else
                (18, 1557702528049664360480)
            else
              if b < 93 then
                (11, 2495464362753)
              else
                if b < 94 then
                  (0, 0)
                else
                  (16, 3679495871196566275)
          else
            if b < 98 then
              if b < 96 then
                (20, 166186942542231134995216)
              else
                if b < 97 then
                  (21, 5158087100764132206649344)
                else
                  (11, 4824124101648)
            else
              if b < 99 then
                (12, 72580920967473)
              else
                if b < 100 then
                  (14, 19552921384468742)
                else
                  (9, 18328536852)
        else
          if b < 106 then
            if b < 103 then
              if b < 102 then
                (17, 136569221165158174720)
              else
                (13, 1201042347022198)
            else
              if b < 104 then
                (11, 4704181878790)
              else
                if b < 105 then
                  (12, 39720679637507)
                else
                  (18, 1318092485783672981254)
          else
            if b < 109 then
              if b < 107 then
                (19, 20500410084691763396640)
              else
                if b < 108 then
                  (11, 7108271752288)
                else
                  (13, 638839643636017)
            else
              if b < 110 then
                (7, 52703280)
              else
                if b < 111 then
                  (11, 7998374507616)
                else
                  (20, 322433265618304771293702)
      else
        if b < 123 then
          if b < 117 then
            if b < 114 then
              if b < 113 then
                (12, 75069390275184)
              else
                (9, 1951863824)
            else
              if b < 115 then
                (9, 13153534208)
              else
                if b < 116 then
                  (15, 316455339320177991)
                else
                  (15, 321817368351212038)
          else
            if b < 120 then
              if b < 118 then
                (19, 24926673828974789346679)
              else
                if b < 119 then
                  (19, 20739217117668862595120)
                else
                  (12, 77189974532096)
            else
              if b < 121 then
                (14, 19215370540028944)
              else
                if b < 122 then
                  (16, 5121740885774696480)
                else
                  (20, 336606274687797737754624)
        else
          if b < 129 then
            if b < 126 then
              if b < 124 then
                (17, 82381890863034925088)
              else
                if b < 125 then
                  (5, 275552)
                else
                  (10, 296439972355)
            else
              if b < 127 then
                (10, 12936482819)
              else
                if b < 128 then
                  (17, 58871933948023603250)
                else
                  (17, 77561891083626152736)
          else
            if b < 132 then
              if b < 130 then
                (11, 4698744768006)
              else
                if b < 131 then
                  (6, 7627830)
                else
                  (17, 81012566866008679219)
            else
              if b < 133 then
                (16, 4919466086949466881)
              else
                if b < 134 then
                  (16, 5125994008114648950)
                else
                  (10, 431497507140)
    else
      if b < 157 then
        if b < 146 then
          if b < 140 then
            if b < 137 then
              if b < 136 then
                (11, 2418338301187)
              else
                (10, 508807108436)
            else
              if b < 138 then
                (10, 137492770864)
              else
                if b < 139 then
                  (17, 40572984019106531073)
                else
                  (14, 19427283923173936)
          else
            if b < 143 then
              if b < 141 then
                (20, 549942496840351444307968)
              else
                if b < 142 then
                  (15, 537994712863293702)
                else
                  (7, 88360791)
            else
              if b < 144 then
                (19, 15071215088215226777635)
              else
                if b < 145 then
                  (12, 75888632995888)
                else
                  (14, 10190699790282801)
        else
          if b < 151 then
            if b < 148 then
              if b < 147 then
                (14, 20114978236735600)
              else
                (11, 7994884896262)
            else
              if b < 149 then
                (10, 155156951043)
              else
                if b < 150 then
                  (13, 1161085677929219)
                else
                  (9, 22569645574)
          else
            if b < 154 then
              if b < 152 then
                (9, 17840751152)
              else
                if b < 153 then
                  (9, 12935364608)
                else
                  (17, 40572984018615668785)
            else
              if b < 155 then
                (18, 2144578115075637837830)
              else
                if b < 156 then
                  (19, 21052884017841371029616)
                else
                  (15, 393015239894974726)
      else
        if b < 168 then
          if b < 162 then
            if b < 159 then
              if b < 158 then
                (15, 163542480555422465)
              else
                (7, 74908416)
            else
              if b < 160 then
                (19, 34371189879753027306871)
              else
                if b < 161 then
                  (13, 1200972787364960)
                else
                  (13, 638838604239666)
          else
            if b < 165 then
              if b < 163 then
                (15, 307484222514467632)
              else
                if b < 164 then
                  (13, 1257046841311494)
                else
                  (9, 31207145798)
            else
              if b < 166 then
                (11, 4535502307632)
              else
                if b < 167 then
                  (14, 18969076397720951)
                else
                  (14, 20059865770041456)
        else
          if b < 174 then
            if b < 171 then
              if b < 169 then
                (13, 1165770894619392)
              else
                if b < 170 then
                  (10, 293205968390)
                else
                  (15, 229968492001452035)
            else
              if b < 172 then
                (13, 635519066505731)
              else
                if b < 173 then
                  (14, 14373030746730548)
                else
                  (11, 5776734438918)
          else
            if b < 177 then
              if b < 175 then
                (22, 144420726633533551174222342)
              else
                if b < 176 then
                  (17, 81232683303098847232)
                else
                  (7, 37892179)
            else
              if b < 178 then
                (16, 3679495871146378291)
              else
                if b < 179 then
                  (17, 41813235709328520704)
                else
                  (14, 19427477126459442)

def treeEdge6 (b : Nat) : Bool :=
  if b < 90 then
    if b < 45 then
      if b < 22 then
        if b < 11 then
          if b < 5 then
            true
          else
            if b < 8 then
              true
            else
              if b < 9 then
                true
              else
                if b < 10 then
                  false
                else
                  true
        else
          if b < 16 then
            true
          else
            if b < 19 then
              true
            else
              if b < 20 then
                true
              else
                if b < 21 then
                  false
                else
                  true
      else
        if b < 33 then
          if b < 27 then
            if b < 24 then
              if b < 23 then
                false
              else
                true
            else
              true
          else
            if b < 30 then
              true
            else
              false
        else
          if b < 39 then
            if b < 36 then
              if b < 34 then
                true
              else
                if b < 35 then
                  true
                else
                  false
            else
              true
          else
            if b < 42 then
              if b < 40 then
                false
              else
                if b < 41 then
                  false
                else
                  true
            else
              if b < 43 then
                true
              else
                if b < 44 then
                  true
                else
                  false
    else
      if b < 67 then
        if b < 56 then
          if b < 50 then
            if b < 47 then
              true
            else
              if b < 48 then
                true
              else
                false
          else
            if b < 53 then
              if b < 51 then
                true
              else
                false
            else
              true
        else
          if b < 61 then
            false
          else
            if b < 64 then
              if b < 62 then
                false
              else
                if b < 63 then
                  false
                else
                  true
            else
              if b < 65 then
                false
              else
                if b < 66 then
                  false
                else
                  true
      else
        if b < 78 then
          if b < 72 then
            if b < 69 then
              if b < 68 then
                true
              else
                false
            else
              false
          else
            if b < 75 then
              if b < 73 then
                false
              else
                true
            else
              false
        else
          if b < 84 then
            false
          else
            if b < 87 then
              if b < 85 then
                false
              else
                if b < 86 then
                  true
                else
                  false
            else
              false
  else
    if b < 135 then
      if b < 112 then
        if b < 101 then
          if b < 95 then
            if b < 92 then
              false
            else
              if b < 93 then
                false
              else
                if b < 94 then
                  true
                else
                  false
          else
            false
        else
          false
      else
        false
    else
      false

def forwardBlocks : Fin 7 → Nat → Nat
  | 0 => forward0Blocks
  | 1 => forward1Blocks
  | 2 => forward2Blocks
  | 3 => forward3Blocks
  | 4 => forward4Blocks
  | 5 => forward5Blocks
  | 6 => forward6Blocks

def transitionForward (a : Fin 7) (r : Fin 180) : Fin 180 :=
  Fin.ofNat 180 (((forwardBlocks a) (r.val / 256) >>> (8 * (r.val % 256))) % 256)

def backwardBlocks : Fin 7 → Nat → Nat
  | 0 => backward0Blocks
  | 1 => backward1Blocks
  | 2 => backward2Blocks
  | 3 => backward3Blocks
  | 4 => backward4Blocks
  | 5 => backward5Blocks
  | 6 => backward6Blocks

def transitionBackward (a : Fin 7) (r : Fin 180) : Fin 180 :=
  Fin.ofNat 180 (((backwardBlocks a) (r.val / 256) >>> (8 * (r.val % 256))) % 256)

def factorCode : Fin 7 → Nat → Nat × Nat
  | 0 => factorCode0
  | 1 => factorCode1
  | 2 => factorCode2
  | 3 => factorCode3
  | 4 => factorCode4
  | 5 => factorCode5
  | 6 => factorCode6

def treeEdge : Fin 7 → Nat → Bool
  | 0 => treeEdge0
  | 1 => treeEdge1
  | 2 => treeEdge2
  | 3 => treeEdge3
  | 4 => treeEdge4
  | 5 => treeEdge5
  | 6 => treeEdge6

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First
