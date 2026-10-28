module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.RowWords

/-!
# Literal lift entries

Untrusted witnesses from the unchanged ATLAS J4G1-max2W1 data of
R. A. Wilson, S. J. Nickerson and J. N. Bray. All uses of these tables
require the kernel certificates. See `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

noncomputable def liftEntry0_part0 (m : ℕ) : ℕ :=
  if m < 3 then
    if m < 1 then
      1
    else
      if m < 2 then
        2
      else
        4
  else
    if m < 5 then
      if m < 4 then
        8
      else
        16
    else
      if m < 6 then
        32
      else
        64

noncomputable def liftEntry0_part1 (m : ℕ) : ℕ :=
  if m < 10 then
    if m < 8 then
      128
    else
      if m < 9 then
        256
      else
        512
  else
    if m < 12 then
      if m < 11 then
        1024
      else
        2048
    else
      if m < 13 then
        4096
      else
        8192

noncomputable def liftEntry0_part2 (m : ℕ) : ℕ :=
  if m < 17 then
    if m < 15 then
      16384
    else
      if m < 16 then
        32768
      else
        65536
  else
    if m < 19 then
      if m < 18 then
        131072
      else
        262144
    else
      if m < 20 then
        524288
      else
        1048576

noncomputable def liftEntry0_part3 (m : ℕ) : ℕ :=
  if m < 24 then
    if m < 22 then
      2097152
    else
      if m < 23 then
        4194304
      else
        8388608
  else
    if m < 26 then
      if m < 25 then
        16777216
      else
        33554432
    else
      if m < 27 then
        67108864
      else
        134217728

noncomputable def liftEntry0_part4 (m : ℕ) : ℕ :=
  if m < 31 then
    if m < 29 then
      268435456
    else
      if m < 30 then
        536870912
      else
        1073741824
  else
    if m < 33 then
      if m < 32 then
        2147483648
      else
        4294967296
    else
      if m < 34 then
        8589934592
      else
        17179869184

noncomputable def liftEntry0_part5 (m : ℕ) : ℕ :=
  if m < 38 then
    if m < 36 then
      34359738368
    else
      if m < 37 then
        68719476736
      else
        137438953472
  else
    if m < 40 then
      if m < 39 then
        274877906944
      else
        549755813888
    else
      if m < 41 then
        1099511627776
      else
        2199023255552

noncomputable def liftEntry0_part6 (m : ℕ) : ℕ :=
  if m < 45 then
    if m < 43 then
      4398046511104
    else
      if m < 44 then
        8796093022208
      else
        17592186044416
  else
    if m < 47 then
      if m < 46 then
        35184372088832
      else
        70368744177664
    else
      if m < 48 then
        140737488355328
      else
        281474976710656

noncomputable def liftEntry0_part7 (m : ℕ) : ℕ :=
  if m < 52 then
    if m < 50 then
      562949953421312
    else
      if m < 51 then
        1125899906842624
      else
        2251799813685248
  else
    if m < 54 then
      if m < 53 then
        4503599627370496
      else
        9007199254740992
    else
      if m < 55 then
        18014398509481984
      else
        36028797018963968

noncomputable def liftEntry0_part8 (m : ℕ) : ℕ :=
  if m < 59 then
    if m < 57 then
      72057594037927936
    else
      if m < 58 then
        144115188075855872
      else
        288230376151711744
  else
    if m < 61 then
      if m < 60 then
        576460752303423488
      else
        1152921504606846976
    else
      if m < 62 then
        2305843009213693952
      else
        4611686018427387904

noncomputable def liftEntry0_part9 (m : ℕ) : ℕ :=
  if m < 66 then
    if m < 64 then
      9223372036854775808
    else
      if m < 65 then
        18446744073709551616
      else
        36893488147419103232
  else
    if m < 68 then
      if m < 67 then
        73786976294838206464
      else
        147573952589676412928
    else
      if m < 69 then
        295147905179352825856
      else
        590295810358705651712

noncomputable def liftEntry0_part10 (m : ℕ) : ℕ :=
  if m < 73 then
    if m < 71 then
      1180591620717411303424
    else
      if m < 72 then
        2361183241434822606848
      else
        4722366482869645213696
  else
    if m < 75 then
      if m < 74 then
        9444732965739290427392
      else
        18889465931478580854784
    else
      if m < 76 then
        37778931862957161709568
      else
        75557863725914323419136

noncomputable def liftEntry0_part11 (m : ℕ) : ℕ :=
  if m < 80 then
    if m < 78 then
      151115727451828646838272
    else
      if m < 79 then
        302231454903657293676544
      else
        604462909807314587353088
  else
    if m < 82 then
      if m < 81 then
        1208925819614629174706176
      else
        2417851639229258349412352
    else
      if m < 83 then
        4835703278458516698824704
      else
        9671406556917033397649408

noncomputable def liftEntry0_part12 (m : ℕ) : ℕ :=
  if m < 87 then
    if m < 85 then
      19342813113834066795298816
    else
      if m < 86 then
        38685626227668133590597632
      else
        77371252455336267181195264
  else
    if m < 89 then
      if m < 88 then
        154742504910672534362390528
      else
        309485009821345068724781056
    else
      if m < 90 then
        618970019642690137449562112
      else
        1237940039285380274899124224

noncomputable def liftEntry0_part13 (m : ℕ) : ℕ :=
  if m < 94 then
    if m < 92 then
      2475880078570760549798248448
    else
      if m < 93 then
        4951760157141521099596496896
      else
        9903520314283042199192993792
  else
    if m < 96 then
      if m < 95 then
        19807040628566084398385987584
      else
        39614081257132168796771975168
    else
      if m < 97 then
        79228162514264337593543950336
      else
        158456325028528675187087900672

noncomputable def liftEntry0_part14 (m : ℕ) : ℕ :=
  if m < 101 then
    if m < 99 then
      316912650057057350374175801344
    else
      if m < 100 then
        633825300114114700748351602688
      else
        1267650600228229401496703205376
  else
    if m < 103 then
      if m < 102 then
        2535301200456458802993406410752
      else
        5070602400912917605986812821504
    else
      if m < 104 then
        10141204801825835211973625643008
      else
        20282409603651670423947251286016

noncomputable def liftEntry0_part15 (m : ℕ) : ℕ :=
  if m < 108 then
    if m < 106 then
      40564819207303340847894502572032
    else
      if m < 107 then
        81129638414606681695789005144064
      else
        162259276829213363391578010288128
  else
    if m < 110 then
      if m < 109 then
        324518553658426726783156020576256
      else
        649037107316853453566312041152512
    else
      if m < 111 then
        1298074214633706907132624082305024
      else
        2596148429267413814265248164610048

noncomputable def liftEntry0 (m : ℕ) : ℕ :=
  if m < 56 then
    if m < 28 then
      if m < 14 then
        if m < 7 then
          liftEntry0_part0 m
        else
          liftEntry0_part1 m
      else
        if m < 21 then
          liftEntry0_part2 m
        else
          liftEntry0_part3 m
    else
      if m < 42 then
        if m < 35 then
          liftEntry0_part4 m
        else
          liftEntry0_part5 m
      else
        if m < 49 then
          liftEntry0_part6 m
        else
          liftEntry0_part7 m
  else
    if m < 84 then
      if m < 70 then
        if m < 63 then
          liftEntry0_part8 m
        else
          liftEntry0_part9 m
      else
        if m < 77 then
          liftEntry0_part10 m
        else
          liftEntry0_part11 m
    else
      if m < 98 then
        if m < 91 then
          liftEntry0_part12 m
        else
          liftEntry0_part13 m
      else
        if m < 105 then
          liftEntry0_part14 m
        else
          liftEntry0_part15 m

noncomputable def liftEntry1_part0 (m : ℕ) : ℕ :=
  if m < 3 then
    if m < 1 then
      1618254526719021593845148537204882
    else
      if m < 2 then
        1028955185486094104508652983445440
      else
        2960417280544042252562586841648293
  else
    if m < 5 then
      if m < 4 then
        4873537574942774523392087386950239
      else
        2731205621992784876709539642960947
    else
      if m < 6 then
        2412353191714572054428673265065765
      else
        1049673658848677799539590817567639

noncomputable def liftEntry1_part1 (m : ℕ) : ℕ :=
  if m < 10 then
    if m < 8 then
      5164569365041175530551827445691877
    else
      if m < 9 then
        4979366827721102125827427548492845
      else
        4782219960448053108284795264381976
  else
    if m < 12 then
      if m < 11 then
        2547530504621634156072942390395636
      else
        5123593373719401825859839354209050
    else
      if m < 13 then
        442861614830722530787928218171330
      else
        2047954062197613110577024850284941

noncomputable def liftEntry1_part2 (m : ℕ) : ℕ :=
  if m < 17 then
    if m < 15 then
      34149636766717423885956359097145
    else
      if m < 16 then
        2302808312188273407506510480243904
      else
        1618064372451701546843536274280155
  else
    if m < 19 then
      if m < 18 then
        2345679076526152644208016483933015
      else
        2129021736040484486821674218094314
    else
      if m < 20 then
        463153626564337967177729444372277
      else
        743230980972469660100312605536077

noncomputable def liftEntry1_part3 (m : ℕ) : ℕ :=
  if m < 24 then
    if m < 22 then
      2895453188376048201834202812803133
    else
      if m < 23 then
        2975837429064481005242243754395267
      else
        1966541782394596414342629141915142
  else
    if m < 26 then
      if m < 25 then
        329676101978451748376034615799058
      else
        2542474303909753860582370414472902
    else
      if m < 27 then
        3955889994167563784387022580144454
      else
        5046749112847377679100544401609296

noncomputable def liftEntry1_part4 (m : ℕ) : ℕ :=
  if m < 31 then
    if m < 29 then
      1626119547453594873413983727010323
    else
      if m < 30 then
        3952387225792474548735314226719114
      else
        4761438609482668821989651914273649
  else
    if m < 33 then
      if m < 32 then
        2300477735258894062633578786689858
      else
        1204351442905286850520542272779335
    else
      if m < 34 then
        1196958347756537531523619266412963
      else
        2510930640889784041296768404581949

noncomputable def liftEntry1_part5 (m : ℕ) : ℕ :=
  if m < 38 then
    if m < 36 then
      5002058388077627965521397273569688
    else
      if m < 37 then
        3312684019359995248742041087555691
      else
        4939507756814417143824489544474341
  else
    if m < 40 then
      if m < 39 then
        3843186945105927361256634339786777
      else
        4697103655764432432787570860251120
    else
      if m < 41 then
        3647541620577504099579096337055179
      else
        389797699961431056000893571394481

noncomputable def liftEntry1_part6 (m : ℕ) : ℕ :=
  if m < 45 then
    if m < 43 then
      2075192764824814433595649917743937
    else
      if m < 44 then
        4827721275828828021416640217455843
      else
        1297072447407780438187145331390474
  else
    if m < 47 then
      if m < 46 then
        1938325919657860606172603853807692
      else
        1616195957415611744608411555474702
    else
      if m < 48 then
        2180394663947071756979436831401992
      else
        209997311173552681054933820565345

noncomputable def liftEntry1_part7 (m : ℕ) : ℕ :=
  if m < 52 then
    if m < 50 then
      2500624702890282037146023501337587
    else
      if m < 51 then
        432415675312442224903782817805742
      else
        2415020749644451800180537665787852
  else
    if m < 54 then
      if m < 53 then
        1009301882249373648140580190926269
      else
        2918495806097251663240048636984443
    else
      if m < 55 then
        4523784080139208918683124249349320
      else
        2452338458032093679614365314536321

noncomputable def liftEntry1_part8 (m : ℕ) : ℕ :=
  if m < 59 then
    if m < 57 then
      4156945302707053126855124748638857
    else
      if m < 58 then
        2641293127037574359314712662291441
      else
        3570172557790999842945348686811329
  else
    if m < 61 then
      if m < 60 then
        2419055222327607180977079558834672
      else
        1486353495660163010312459722006222
    else
      if m < 62 then
        2701408232911838949176481743705269
      else
        3504247167903592237048468461982860

noncomputable def liftEntry1_part9 (m : ℕ) : ℕ :=
  if m < 66 then
    if m < 64 then
      448445199700138905953490679046375
    else
      if m < 65 then
        1167133663357011225753839242544597
      else
        2949488322104704943823878895811007
  else
    if m < 68 then
      if m < 67 then
        1661403248296390157681263720732637
      else
        1709000408517973667844949550976140
    else
      if m < 69 then
        1020713200003990074072360399366124
      else
        4451762733936035649202032327727930

noncomputable def liftEntry1_part10 (m : ℕ) : ℕ :=
  if m < 73 then
    if m < 71 then
      1140013836419952110006482317862234
    else
      if m < 72 then
        1039725807054673546710208832449681
      else
        1469582058127963450242624112010659
  else
    if m < 75 then
      if m < 74 then
        3078413830962048798295278249158554
      else
        591607405425570313469609893446493
    else
      if m < 76 then
        4493450220396956053231361568518584
      else
        4306547759559737789921807581351609

noncomputable def liftEntry1_part11 (m : ℕ) : ℕ :=
  if m < 80 then
    if m < 78 then
      1579099737534684609355837633244914
    else
      if m < 79 then
        1871818976109271907873143922430084
      else
        859502050065485936611156484667431
  else
    if m < 82 then
      if m < 81 then
        174235819952500321121653879160444
      else
        749972426327335851743914035532163
    else
      if m < 83 then
        1307629229362152392228874154966854
      else
        322309389257662496795584377890148

noncomputable def liftEntry1_part12 (m : ℕ) : ℕ :=
  if m < 87 then
    if m < 85 then
      2185124939806206128403714993984903
    else
      if m < 86 then
        2876074268653565316072105878907917
      else
        2938497723649665361829379634906994
  else
    if m < 89 then
      if m < 88 then
        3273574808677544328935160131043964
      else
        675032933482116803661057700154266
    else
      if m < 90 then
        1059097183953004099873280396684222
      else
        797178986698811243034835628152493

noncomputable def liftEntry1_part13 (m : ℕ) : ℕ :=
  if m < 94 then
    if m < 92 then
      1862118934655427751693485649316341
    else
      if m < 93 then
        552489228785301826475201334338983
      else
        3586569035215555553181556040536678
  else
    if m < 96 then
      if m < 95 then
        2023710218134990176984640848316200
      else
        3791376795770040568425382744488930
    else
      if m < 97 then
        2834183868427607220417361515836888
      else
        2460748563499866116124232399164127

noncomputable def liftEntry1_part14 (m : ℕ) : ℕ :=
  if m < 101 then
    if m < 99 then
      1599971675533611769499657289102939
    else
      if m < 100 then
        4393559289468913259078287572328735
      else
        338112314113224368881108403195873
  else
    if m < 103 then
      if m < 102 then
        1205116587017664860405979573112946
      else
        1456370335668674574588142607458107
    else
      if m < 104 then
        3256833983492099386032437405178196
      else
        1246059866429223477838471867808188

noncomputable def liftEntry1_part15 (m : ℕ) : ℕ :=
  if m < 108 then
    if m < 106 then
      3492866252203416461229115289267183
    else
      if m < 107 then
        26658043140281242639750693716598
      else
        2037789549235526587979063141388802
  else
    if m < 110 then
      if m < 109 then
        364790427033962765381843919717756
      else
        3917814646305653764453408913478001
    else
      if m < 111 then
        3429911828893664307133725169783082
      else
        26178872704669264730766045978228

noncomputable def liftEntry1 (m : ℕ) : ℕ :=
  if m < 56 then
    if m < 28 then
      if m < 14 then
        if m < 7 then
          liftEntry1_part0 m
        else
          liftEntry1_part1 m
      else
        if m < 21 then
          liftEntry1_part2 m
        else
          liftEntry1_part3 m
    else
      if m < 42 then
        if m < 35 then
          liftEntry1_part4 m
        else
          liftEntry1_part5 m
      else
        if m < 49 then
          liftEntry1_part6 m
        else
          liftEntry1_part7 m
  else
    if m < 84 then
      if m < 70 then
        if m < 63 then
          liftEntry1_part8 m
        else
          liftEntry1_part9 m
      else
        if m < 77 then
          liftEntry1_part10 m
        else
          liftEntry1_part11 m
    else
      if m < 98 then
        if m < 91 then
          liftEntry1_part12 m
        else
          liftEntry1_part13 m
      else
        if m < 105 then
          liftEntry1_part14 m
        else
          liftEntry1_part15 m

noncomputable def liftEntry2_part0 (m : ℕ) : ℕ :=
  if m < 3 then
    if m < 1 then
      3661340251039437499245774961440397
    else
      if m < 2 then
        1981470332376759938269321289391404
      else
        645969891560035096777839914983148
  else
    if m < 5 then
      if m < 4 then
        3892403455377368923370103153592550
      else
        1448398457706090429399513034194704
    else
      if m < 6 then
        4506679401571513895151631047521595
      else
        4586970722190207818673888008177979

noncomputable def liftEntry2_part1 (m : ℕ) : ℕ :=
  if m < 10 then
    if m < 8 then
      3846076293399273058186913356631434
    else
      if m < 9 then
        260894688135095298260857879298054
      else
        4158046104266381008187804480525393
  else
    if m < 12 then
      if m < 11 then
        361392337060302267462190121459245
      else
        444278040950446827611188676814630
    else
      if m < 13 then
        4333976482460518663618600126925897
      else
        637558768689326810099647093812542

noncomputable def liftEntry2_part2 (m : ℕ) : ℕ :=
  if m < 17 then
    if m < 15 then
      217043966839686061454057030917644
    else
      if m < 16 then
        4389874709377727087936593880531304
      else
        4331754084641951942101580995987654
  else
    if m < 19 then
      if m < 18 then
        4592653780356320713866831519283925
      else
        4372844613595913720294528332715752
    else
      if m < 20 then
        2548996808807952895664167327470731
      else
        4301500314154491943148669572078296

noncomputable def liftEntry2_part3 (m : ℕ) : ℕ :=
  if m < 24 then
    if m < 22 then
      605656600714424253495354987422953
    else
      if m < 23 then
        4491020549084879815956126085388965
      else
        94019497583613457527841548384977
  else
    if m < 26 then
      if m < 25 then
        309720874878869049126301840014782
      else
        4050020705387958747448726919071100
    else
      if m < 27 then
        2760882820822623807682872162149142
      else
        3699441854524126506192993013667574

noncomputable def liftEntry2_part4 (m : ℕ) : ℕ :=
  if m < 31 then
    if m < 29 then
      2003738208568463690923764521543819
    else
      if m < 30 then
        909268875864907332380390354140986
      else
        1446352378848608189564966548422450
  else
    if m < 33 then
      if m < 32 then
        1948794773771054592293581822116699
      else
        2614327546265781218405739508514723
    else
      if m < 34 then
        965718468944816286689935242004806
      else
        3829303285682642891743524650418960

noncomputable def liftEntry2_part5 (m : ℕ) : ℕ :=
  if m < 38 then
    if m < 36 then
      2716613907795173726602466299060430
    else
      if m < 37 then
        1005835325224613013858142759574375
      else
        2646689756070585622784268848335463
  else
    if m < 40 then
      if m < 39 then
        2412753642107459010964028901644950
      else
        1768600230392674117349570368852677
    else
      if m < 41 then
        1246273051289710715259463928131775
      else
        2075355905622873944685472888294045

noncomputable def liftEntry2_part6 (m : ℕ) : ℕ :=
  if m < 45 then
    if m < 43 then
      2791232440874826966042366731115722
    else
      if m < 44 then
        408450090197029409622638355612219
      else
        3570812242413438650582464252035513
  else
    if m < 47 then
      if m < 46 then
        4543894253631046866345800257151511
      else
        395285175573362997847641003115244
    else
      if m < 48 then
        3940286933134202226215834790511753
      else
        3277957089008800423904656795109365

noncomputable def liftEntry2_part7 (m : ℕ) : ℕ :=
  if m < 52 then
    if m < 50 then
      179496410237327913814021356868593
    else
      if m < 51 then
        5147450376377490420007834936381417
      else
        1209806103168465261550624027069857
  else
    if m < 54 then
      if m < 53 then
        4006865609994286843715615031900149
      else
        2089924081771611346383783117631220
    else
      if m < 55 then
        3310319399806237420375295318413622
      else
        626282095508046962395613918323395

noncomputable def liftEntry2_part8 (m : ℕ) : ℕ :=
  if m < 59 then
    if m < 57 then
      4846884851207492712222450847747965
    else
      if m < 58 then
        4916281352950486205036458258205489
      else
        2802286393957080165294427037097243
  else
    if m < 61 then
      if m < 60 then
        5082426949742457416469762584755757
      else
        5033811525037218411630260619526747
    else
      if m < 62 then
        2557920100035285300764226052161020
      else
        3909075627113263134317374491555978

noncomputable def liftEntry2_part9 (m : ℕ) : ℕ :=
  if m < 66 then
    if m < 64 then
      5191702833220475248609442004982675
    else
      if m < 65 then
        3104207610904276592858712206978387
      else
        1365730976955583601301227513730567
  else
    if m < 68 then
      if m < 67 then
        2038532681294606947204999821836844
      else
        4415839560224752795122342001853935
    else
      if m < 69 then
        318141043509765570581594102619667
      else
        941350905220918278182783795476105

noncomputable def liftEntry2_part10 (m : ℕ) : ℕ :=
  if m < 73 then
    if m < 71 then
      462690167928985622635361505910208
    else
      if m < 72 then
        3847545820120092677779189414496871
      else
        1824621115432796612368052699767644
  else
    if m < 75 then
      if m < 74 then
        339535638594813286217706905295475
      else
        3241580205702163692748008109815822
    else
      if m < 76 then
        4983980043495858728021713339971658
      else
        1258728886212372056383355701158284

noncomputable def liftEntry2_part11 (m : ℕ) : ℕ :=
  if m < 80 then
    if m < 78 then
      227498902372984683027191725865014
    else
      if m < 79 then
        2953743195283660753126916548844155
      else
        579700215671926971371785241071791
  else
    if m < 82 then
      if m < 81 then
        2690070086725887765625525984289212
      else
        1476741050558043365748982440290914
    else
      if m < 83 then
        490773362043135527311095542093682
      else
        2451194863752167553773128751207019

noncomputable def liftEntry2_part12 (m : ℕ) : ℕ :=
  if m < 87 then
    if m < 85 then
      4321253066332337797521650136368677
    else
      if m < 86 then
        3818635125825841395943362490561178
      else
        5180356420224941950118583154787027
  else
    if m < 89 then
      if m < 88 then
        225628000930530864237543575428007
      else
        2373118759692781170414818924763221
    else
      if m < 90 then
        5104537465078545746318234228520104
      else
        915297417630571211836136533767689

noncomputable def liftEntry2_part13 (m : ℕ) : ℕ :=
  if m < 94 then
    if m < 92 then
      1338299858657458425816066784635811
    else
      if m < 93 then
        3284947526689063855718310525140206
      else
        1342611810806143528552915943073865
  else
    if m < 96 then
      if m < 95 then
        4261709934955692821766251912476104
      else
        1527445720288722972777685683938304
    else
      if m < 97 then
        3104738415873580503025611514292806
      else
        2702980579149096068702193955048116

noncomputable def liftEntry2_part14 (m : ℕ) : ℕ :=
  if m < 101 then
    if m < 99 then
      4081518442783135907931183718745758
    else
      if m < 100 then
        2361343917109436089646851078859968
      else
        4022042795936435676761815384428715
  else
    if m < 103 then
      if m < 102 then
        2704500258028146029092486333029692
      else
        1753373751957463953425594698063989
    else
      if m < 104 then
        1040892715770778218756784487399286
      else
        3699307620446295008122733153057504

noncomputable def liftEntry2_part15 (m : ℕ) : ℕ :=
  if m < 108 then
    if m < 106 then
      4828550289467339848199918580440363
    else
      if m < 107 then
        4624711903677615417738072765954304
      else
        4649906717076513397988758565142010
  else
    if m < 110 then
      if m < 109 then
        3397473066268090276615479285206074
      else
        4472354634350068508116916483844418
    else
      if m < 111 then
        3437186883502557784961464211715083
      else
        2816284244249520175351688140116593

noncomputable def liftEntry2 (m : ℕ) : ℕ :=
  if m < 56 then
    if m < 28 then
      if m < 14 then
        if m < 7 then
          liftEntry2_part0 m
        else
          liftEntry2_part1 m
      else
        if m < 21 then
          liftEntry2_part2 m
        else
          liftEntry2_part3 m
    else
      if m < 42 then
        if m < 35 then
          liftEntry2_part4 m
        else
          liftEntry2_part5 m
      else
        if m < 49 then
          liftEntry2_part6 m
        else
          liftEntry2_part7 m
  else
    if m < 84 then
      if m < 70 then
        if m < 63 then
          liftEntry2_part8 m
        else
          liftEntry2_part9 m
      else
        if m < 77 then
          liftEntry2_part10 m
        else
          liftEntry2_part11 m
    else
      if m < 98 then
        if m < 91 then
          liftEntry2_part12 m
        else
          liftEntry2_part13 m
      else
        if m < 105 then
          liftEntry2_part14 m
        else
          liftEntry2_part15 m

noncomputable def liftEntry3_part0 (m : ℕ) : ℕ :=
  if m < 3 then
    if m < 1 then
      4229966212328748098007725794563495
    else
      if m < 2 then
        1642238114221998587616170916394131
      else
        3609115767576240443770105852466593
  else
    if m < 5 then
      if m < 4 then
        2963199758688011246845095899685835
      else
        4259388753405959121442616957764717
    else
      if m < 6 then
        2481494212670211768112346532851076
      else
        3947991527507945831029185662126329

noncomputable def liftEntry3_part1 (m : ℕ) : ℕ :=
  if m < 10 then
    if m < 8 then
      2302355857335520441019954505918137
    else
      if m < 9 then
        3176495331704789270377326209187610
      else
        3923735402332691794557146112734876
  else
    if m < 12 then
      if m < 11 then
        4795615943532399665258376823091950
      else
        3393031827209898424253157167485757
    else
      if m < 13 then
        4246200997140674603392569309747559
      else
        1208610186305207149904235834711696

noncomputable def liftEntry3_part2 (m : ℕ) : ℕ :=
  if m < 17 then
    if m < 15 then
      3603146334721601354615991249343590
    else
      if m < 16 then
        4809878032870644007834025287917848
      else
        1979274880093588047759184060496909
  else
    if m < 19 then
      if m < 18 then
        301367769908677897996083720240801
      else
        933791029245082370342219762923471
    else
      if m < 20 then
        177730143373496996413174996273885
      else
        1872733345167490098202348287677025

noncomputable def liftEntry3_part3 (m : ℕ) : ℕ :=
  if m < 24 then
    if m < 22 then
      1981988688385130731614516456848826
    else
      if m < 23 then
        3651479300342356685664644141977077
      else
        3986267905058849139798410251066205
  else
    if m < 26 then
      if m < 25 then
        2971126989415303092466867305562863
      else
        2055772931565215376254155779450510
    else
      if m < 27 then
        2546162067083962992985918888917004
      else
        3569263674136470186740756380779020

noncomputable def liftEntry3_part4 (m : ℕ) : ℕ :=
  if m < 31 then
    if m < 29 then
      2907288839252224930702499701065688
    else
      if m < 30 then
        1883517666385021134911494146257273
      else
        1734832209232344261554110999918821
  else
    if m < 33 then
      if m < 32 then
        1943980684950919482739804198176704
      else
        4408679345173881933830304971511924
    else
      if m < 34 then
        3435076144742476374192469369027710
      else
        765918367208522688886093388032977

noncomputable def liftEntry3_part5 (m : ℕ) : ℕ :=
  if m < 38 then
    if m < 36 then
      893878583278164769090676775032918
    else
      if m < 37 then
        2991991037104903035972187303628784
      else
        373863750106090282101607062124212
  else
    if m < 40 then
      if m < 39 then
        1572755256218620693856379177167241
      else
        798899366920130509089292702478207
    else
      if m < 41 then
        606260060843336412469709200221555
      else
        4047656936508588680367332882535281

noncomputable def liftEntry3_part6 (m : ℕ) : ℕ :=
  if m < 45 then
    if m < 43 then
      2123330623945568850809512280327661
    else
      if m < 44 then
        4326565280345481106866171386384256
      else
        2216540463525515961851673410686689
  else
    if m < 47 then
      if m < 46 then
        4735592155809050394388852587424841
      else
        865226745540423921954481169671687
    else
      if m < 48 then
        1367013279387945179028533151070737
      else
        3428141545486498516888960355736074

noncomputable def liftEntry3_part7 (m : ℕ) : ℕ :=
  if m < 52 then
    if m < 50 then
      65818367165156486602106996961865
    else
      if m < 51 then
        1596508498660922757701421749444020
      else
        4613379017795448051962273054882379
  else
    if m < 54 then
      if m < 53 then
        3082804095545096118399540120507169
      else
        3187881493168924242066648112059188
    else
      if m < 55 then
        982484327121563805072566528405253
      else
        1314148651948940734745931883826019

noncomputable def liftEntry3_part8 (m : ℕ) : ℕ :=
  if m < 59 then
    if m < 57 then
      1197028962126682885217515967957319
    else
      if m < 58 then
        3220553277751139936294340433875911
      else
        540986147111001847644094194766609
  else
    if m < 61 then
      if m < 60 then
        1802807144752214114214832515717527
      else
        4879813651530945317655906201383669
    else
      if m < 62 then
        2066681487376263326104935854898215
      else
        4021834363006084527317784972368692

noncomputable def liftEntry3_part9 (m : ℕ) : ℕ :=
  if m < 66 then
    if m < 64 then
      1249324861114415245609642305431800
    else
      if m < 65 then
        701593749999817825902163472085198
      else
        3653343812373555825449065514434551
  else
    if m < 68 then
      if m < 67 then
        3377274423693775443572184143073488
      else
        2984840872421787701811954778999793
    else
      if m < 69 then
        1121836070116535154556812761558998
      else
        1306419361559464727201094623923663

noncomputable def liftEntry3_part10 (m : ℕ) : ℕ :=
  if m < 73 then
    if m < 71 then
      2508423006804050540095542072964042
    else
      if m < 72 then
        3004176350279159161712545826996733
      else
        3324943004976745357056301780374700
  else
    if m < 75 then
      if m < 74 then
        1973605488821506631027569084942805
      else
        1826364714322751744699424736478183
    else
      if m < 76 then
        1055176364286844671216409663823234
      else
        2344986832662451640572331222992300

noncomputable def liftEntry3_part11 (m : ℕ) : ℕ :=
  if m < 80 then
    if m < 78 then
      897554543367020046762097420076653
    else
      if m < 79 then
        2829609849296920742293776216730918
      else
        3974439921700076767345160641392518
  else
    if m < 82 then
      if m < 81 then
        2524647965042415136499241482964972
      else
        2673336129156069994326458756030754
    else
      if m < 83 then
        2934802321678111265624183050478823
      else
        5167259799958764533375877624467663

noncomputable def liftEntry3_part12 (m : ℕ) : ℕ :=
  if m < 87 then
    if m < 85 then
      3005975482826338595230637605697199
    else
      if m < 86 then
        3309294571179926792540382576620070
      else
        2507617104905201443408288910339827
  else
    if m < 89 then
      if m < 88 then
        4184180549613047132368637035039490
      else
        2985722347303333035201689359018834
    else
      if m < 90 then
        2464536239347452944519725024453664
      else
        2813542517528136010542963071148487

noncomputable def liftEntry3_part13 (m : ℕ) : ℕ :=
  if m < 94 then
    if m < 92 then
      197598601502631679392985171101381
    else
      if m < 93 then
        408137723554144124191721224343562
      else
        1936450011134537444827092566283178
  else
    if m < 96 then
      if m < 95 then
        1189100546608131382887054303311859
      else
        3789176462853970249834685948112951
    else
      if m < 97 then
        4421412966353717975237055334729636
      else
        1988314801025309719569198984257544

noncomputable def liftEntry3_part14 (m : ℕ) : ℕ :=
  if m < 101 then
    if m < 99 then
      5162143080858603711881325721712859
    else
      if m < 100 then
        1354172046559475165865789946101723
      else
        323906285932990034788160344489591
  else
    if m < 103 then
      if m < 102 then
        1243836136222379316332065804455427
      else
        4038721759349549051813020621855401
    else
      if m < 104 then
        5043905998734054058164387160325988
      else
        3046947973769774834698291389849451

noncomputable def liftEntry3_part15 (m : ℕ) : ℕ :=
  if m < 108 then
    if m < 106 then
      1862740391127690331447909926164631
    else
      if m < 107 then
        2161455053856683266974645046450047
      else
        1804225859727885810217360216924212
  else
    if m < 110 then
      if m < 109 then
        3203195247442382695432565686907068
      else
        1210416449893013212899505654853219
    else
      if m < 111 then
        626264646292309381212325440391437
      else
        3187975796615105086780316763349608

noncomputable def liftEntry3 (m : ℕ) : ℕ :=
  if m < 56 then
    if m < 28 then
      if m < 14 then
        if m < 7 then
          liftEntry3_part0 m
        else
          liftEntry3_part1 m
      else
        if m < 21 then
          liftEntry3_part2 m
        else
          liftEntry3_part3 m
    else
      if m < 42 then
        if m < 35 then
          liftEntry3_part4 m
        else
          liftEntry3_part5 m
      else
        if m < 49 then
          liftEntry3_part6 m
        else
          liftEntry3_part7 m
  else
    if m < 84 then
      if m < 70 then
        if m < 63 then
          liftEntry3_part8 m
        else
          liftEntry3_part9 m
      else
        if m < 77 then
          liftEntry3_part10 m
        else
          liftEntry3_part11 m
    else
      if m < 98 then
        if m < 91 then
          liftEntry3_part12 m
        else
          liftEntry3_part13 m
      else
        if m < 105 then
          liftEntry3_part14 m
        else
          liftEntry3_part15 m

noncomputable def liftEntry : Fin 4 → ℕ → ℕ :=
  ![liftEntry0, liftEntry1, liftEntry2, liftEntry3]

set_option maxRecDepth 10000 in
private theorem lift_checked : ∀ (j : Fin 4) (i : Fin 112),
    liftEntry j i.val = if j = 0 then 2^i.val else (liftRows j).get i := by
  decide +kernel

theorem liftEntry_checked (j : Fin 4) (i : Fin 112) :
    liftEntry j i.val = (liftRows j).get i := by
  rw [lift_checked]
  split
  · next h => subst j; simp [liftRows, packedOne, get_ofFn]
  · rfl

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
