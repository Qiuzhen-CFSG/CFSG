module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair10
import Mathlib.Tactic.FinCases

/-!
# A conjugator for two literal two-subgroups

The literal ATLAS degree-2058 action certifies every identity by kernel
reduction in bounded blocks. No numerical GAP output is a proof premise.
Sources: HeG1-p2058B0, max3/max4 programs, and LocalActions/source/Explore.g.
Reproduction: Factors/source/generate.py; proposed series: ../source/pcdata.json.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair10Conjugacy
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

def conjugator_forward_0 (x : ℕ) : ℕ :=
  (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then 276 else 282) else (if x < 3 then 609 else 1406)) else (if x < 6 then (if x < 5 then 1025 else 1843) else (if x < 7 then 1801 else 428))) else (if x < 12 then (if x < 10 then (if x < 9 then 1595 else 1193) else (if x < 11 then 421 else 577)) else (if x < 14 then (if x < 13 then 700 else 1059) else (if x < 15 then 446 else 924)))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then 869 else 1591) else (if x < 19 then 806 else 1336)) else (if x < 22 then (if x < 21 then 674 else 1062) else (if x < 23 then 473 else 663))) else (if x < 28 then (if x < 26 then (if x < 25 then 2056 else 1453) else (if x < 27 then 1139 else 333)) else (if x < 30 then (if x < 29 then 2008 else 438) else (if x < 31 then 1588 else 1434))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then 820 else 546) else (if x < 35 then 794 else 940)) else (if x < 38 then (if x < 37 then 1039 else 395) else (if x < 39 then 1333 else 377))) else (if x < 44 then (if x < 42 then (if x < 41 then 1413 else 563) else (if x < 43 then 1090 else 892)) else (if x < 46 then (if x < 45 then 897 else 179) else (if x < 47 then 1752 else 1040)))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then 1867 else 529) else (if x < 51 then 1525 else 13)) else (if x < 54 then (if x < 53 then 1909 else 80) else (if x < 55 then 1875 else 1726))) else (if x < 60 then (if x < 58 then (if x < 57 then 992 else 1010) else (if x < 59 then 296 else 1168)) else (if x < 62 then (if x < 61 then 157 else 452) else (if x < 63 then 416 else 484))))))

def conjugator_forward_64 (x : ℕ) : ℕ :=
  (if x < 96 then (if x < 80 then (if x < 72 then (if x < 68 then (if x < 66 then (if x < 65 then 1673 else 1067) else (if x < 67 then 1641 else 1846)) else (if x < 70 then (if x < 69 then 1857 else 1021) else (if x < 71 then 1729 else 375))) else (if x < 76 then (if x < 74 then (if x < 73 then 652 else 1279) else (if x < 75 then 728 else 297)) else (if x < 78 then (if x < 77 then 1294 else 1407) else (if x < 79 then 1049 else 1172)))) else (if x < 88 then (if x < 84 then (if x < 82 then (if x < 81 then 1104 else 330) else (if x < 83 then 360 else 977)) else (if x < 86 then (if x < 85 then 1345 else 455) else (if x < 87 then 917 else 1636))) else (if x < 92 then (if x < 90 then (if x < 89 then 1109 else 513) else (if x < 91 then 547 else 1714)) else (if x < 94 then (if x < 93 then 1371 else 1976) else (if x < 95 then 292 else 346))))) else (if x < 112 then (if x < 104 then (if x < 100 then (if x < 98 then (if x < 97 then 1216 else 341) else (if x < 99 then 699 else 1983)) else (if x < 102 then (if x < 101 then 668 else 373) else (if x < 103 then 1089 else 545))) else (if x < 108 then (if x < 106 then (if x < 105 then 1455 else 1027) else (if x < 107 then 1944 else 1442)) else (if x < 110 then (if x < 109 then 764 else 109) else (if x < 111 then 1063 else 1425)))) else (if x < 120 then (if x < 116 then (if x < 114 then (if x < 113 then 531 else 362) else (if x < 115 then 104 else 876)) else (if x < 118 then (if x < 117 then 2034 else 203) else (if x < 119 then 778 else 434))) else (if x < 124 then (if x < 122 then (if x < 121 then 1560 else 439) else (if x < 123 then 490 else 1712)) else (if x < 126 then (if x < 125 then 1593 else 975) else (if x < 127 then 1398 else 403))))))

def conjugator_forward_128 (x : ℕ) : ℕ :=
  (if x < 160 then (if x < 144 then (if x < 136 then (if x < 132 then (if x < 130 then (if x < 129 then 492 else 337) else (if x < 131 then 1116 else 354)) else (if x < 134 then (if x < 133 then 858 else 219) else (if x < 135 then 702 else 1004))) else (if x < 140 then (if x < 138 then (if x < 137 then 954 else 675) else (if x < 139 then 949 else 639)) else (if x < 142 then (if x < 141 then 3 else 254) else (if x < 143 then 640 else 1893)))) else (if x < 152 then (if x < 148 then (if x < 146 then (if x < 145 then 1052 else 1271) else (if x < 147 then 984 else 1547)) else (if x < 150 then (if x < 149 then 50 else 1411) else (if x < 151 then 34 else 1360))) else (if x < 156 then (if x < 154 then (if x < 153 then 1245 else 669) else (if x < 155 then 1786 else 849)) else (if x < 158 then (if x < 157 then 258 else 1303) else (if x < 159 then 1152 else 932))))) else (if x < 176 then (if x < 168 then (if x < 164 then (if x < 162 then (if x < 161 then 671 else 772) else (if x < 163 then 301 else 1246)) else (if x < 166 then (if x < 165 then 591 else 987) else (if x < 167 then 512 else 1612))) else (if x < 172 then (if x < 170 then (if x < 169 then 1657 else 230) else (if x < 171 then 393 else 1679)) else (if x < 174 then (if x < 173 then 1606 else 1489) else (if x < 175 then 2047 else 306)))) else (if x < 184 then (if x < 180 then (if x < 178 then (if x < 177 then 1670 else 805) else (if x < 179 then 370 else 1828)) else (if x < 182 then (if x < 181 then 1034 else 963) else (if x < 183 then 812 else 684))) else (if x < 188 then (if x < 186 then (if x < 185 then 1865 else 309) else (if x < 187 then 424 else 1803)) else (if x < 190 then (if x < 189 then 1877 else 334) else (if x < 191 then 1576 else 605))))))

def conjugator_forward_192 (x : ℕ) : ℕ :=
  (if x < 224 then (if x < 208 then (if x < 200 then (if x < 196 then (if x < 194 then (if x < 193 then 1784 else 1015) else (if x < 195 then 238 else 78)) else (if x < 198 then (if x < 197 then 1479 else 999) else (if x < 199 then 263 else 231))) else (if x < 204 then (if x < 202 then (if x < 201 then 1351 else 1739) else (if x < 203 then 470 else 1226)) else (if x < 206 then (if x < 205 then 516 else 58) else (if x < 207 then 1476 else 543)))) else (if x < 216 then (if x < 212 then (if x < 210 then (if x < 209 then 1552 else 1776) else (if x < 211 then 314 else 77)) else (if x < 214 then (if x < 213 then 1092 else 1121) else (if x < 215 then 829 else 564))) else (if x < 220 then (if x < 218 then (if x < 217 then 273 else 1916) else (if x < 219 then 425 else 1756)) else (if x < 222 then (if x < 221 then 786 else 1753) else (if x < 223 then 1507 else 941))))) else (if x < 240 then (if x < 232 then (if x < 228 then (if x < 226 then (if x < 225 then 989 else 9) else (if x < 227 then 1266 else 1339)) else (if x < 230 then (if x < 229 then 1913 else 1988) else (if x < 231 then 167 else 1830))) else (if x < 236 then (if x < 234 then (if x < 233 then 1402 else 1084) else (if x < 235 then 1927 else 1892)) else (if x < 238 then (if x < 237 then 447 else 1135) else (if x < 239 then 985 else 1469)))) else (if x < 248 then (if x < 244 then (if x < 242 then (if x < 241 then 435 else 340) else (if x < 243 then 612 else 1256)) else (if x < 246 then (if x < 245 then 1718 else 838) else (if x < 247 then 1749 else 1737))) else (if x < 252 then (if x < 250 then (if x < 249 then 1814 else 1862) else (if x < 251 then 1456 else 996)) else (if x < 254 then (if x < 253 then 1205 else 517) else (if x < 255 then 738 else 784))))))

def conjugator_forward_256 (x : ℕ) : ℕ :=
  (if x < 288 then (if x < 272 then (if x < 264 then (if x < 260 then (if x < 258 then (if x < 257 then 491 else 817) else (if x < 259 then 407 else 1587)) else (if x < 262 then (if x < 261 then 122 else 244) else (if x < 263 then 904 else 1033))) else (if x < 268 then (if x < 266 then (if x < 265 then 890 else 234) else (if x < 267 then 654 else 1643)) else (if x < 270 then (if x < 269 then 1559 else 18) else (if x < 271 then 1821 else 1450)))) else (if x < 280 then (if x < 276 then (if x < 274 then (if x < 273 then 770 else 1518) else (if x < 275 then 358 else 214)) else (if x < 278 then (if x < 277 then 1110 else 1123) else (if x < 279 then 773 else 548))) else (if x < 284 then (if x < 282 then (if x < 281 then 1186 else 1057) else (if x < 283 then 1420 else 356)) else (if x < 286 then (if x < 285 then 1285 else 584) else (if x < 287 then 1886 else 1214))))) else (if x < 304 then (if x < 296 then (if x < 292 then (if x < 290 then (if x < 289 then 1879 else 1839) else (if x < 291 then 788 else 166)) else (if x < 294 then (if x < 293 then 1890 else 1662) else (if x < 295 then 52 else 7))) else (if x < 300 then (if x < 298 then (if x < 297 then 2055 else 568) else (if x < 299 then 1852 else 791)) else (if x < 302 then (if x < 301 then 970 else 1987) else (if x < 303 then 1697 else 1557)))) else (if x < 312 then (if x < 308 then (if x < 306 then (if x < 305 then 823 else 689) else (if x < 307 then 1761 else 853)) else (if x < 310 then (if x < 309 then 2014 else 1332) else (if x < 311 then 1931 else 1978))) else (if x < 316 then (if x < 314 then (if x < 313 then 1511 else 6) else (if x < 315 then 1041 else 628)) else (if x < 318 then (if x < 317 then 1631 else 192) else (if x < 319 then 1132 else 226))))))

def conjugator_forward_320 (x : ℕ) : ℕ :=
  (if x < 352 then (if x < 336 then (if x < 328 then (if x < 324 then (if x < 322 then (if x < 321 then 1570 else 1098) else (if x < 323 then 1579 else 1239)) else (if x < 326 then (if x < 325 then 262 else 1207) else (if x < 327 then 537 else 185))) else (if x < 332 then (if x < 330 then (if x < 329 then 327 else 366) else (if x < 331 then 138 else 115)) else (if x < 334 then (if x < 333 then 1311 else 1095) else (if x < 335 then 1208 else 70)))) else (if x < 344 then (if x < 340 then (if x < 338 then (if x < 337 then 2003 else 943) else (if x < 339 then 1861 else 520)) else (if x < 342 then (if x < 341 then 1357 else 1535) else (if x < 343 then 1581 else 1337))) else (if x < 348 then (if x < 346 then (if x < 345 then 278 else 1347) else (if x < 347 then 305 else 1855)) else (if x < 350 then (if x < 349 then 871 else 431) else (if x < 351 then 59 else 696))))) else (if x < 368 then (if x < 360 then (if x < 356 then (if x < 354 then (if x < 353 then 1077 else 99) else (if x < 355 then 1958 else 1343)) else (if x < 358 then (if x < 357 then 736 else 1646) else (if x < 359 then 857 else 1797))) else (if x < 364 then (if x < 362 then (if x < 361 then 433 else 1286) else (if x < 363 then 727 else 1915)) else (if x < 366 then (if x < 365 then 1270 else 506) else (if x < 367 then 1159 else 1385)))) else (if x < 376 then (if x < 372 then (if x < 370 then (if x < 369 then 328 else 1319) else (if x < 371 then 232 else 1233)) else (if x < 374 then (if x < 373 then 432 else 629) else (if x < 375 then 310 else 27))) else (if x < 380 then (if x < 378 then (if x < 377 then 570 else 1519) else (if x < 379 then 1028 else 69)) else (if x < 382 then (if x < 381 then 760 else 697) else (if x < 383 then 1200 else 1368))))))

def conjugator_forward_384 (x : ℕ) : ℕ :=
  (if x < 416 then (if x < 400 then (if x < 392 then (if x < 388 then (if x < 386 then (if x < 385 then 1745 else 1671) else (if x < 387 then 488 else 819)) else (if x < 390 then (if x < 389 then 859 else 1554) else (if x < 391 then 919 else 524))) else (if x < 396 then (if x < 394 then (if x < 393 then 549 else 804) else (if x < 395 then 191 else 212)) else (if x < 398 then (if x < 397 then 353 else 71) else (if x < 399 then 1377 else 221)))) else (if x < 408 then (if x < 404 then (if x < 402 then (if x < 401 then 807 else 1690) else (if x < 403 then 4 else 1228)) else (if x < 406 then (if x < 405 then 994 else 928) else (if x < 407 then 752 else 487))) else (if x < 412 then (if x < 410 then (if x < 409 then 1532 else 1992) else (if x < 411 then 1463 else 750)) else (if x < 414 then (if x < 413 then 960 else 1272) else (if x < 415 then 861 else 359))))) else (if x < 432 then (if x < 424 then (if x < 420 then (if x < 418 then (if x < 417 then 347 else 324) else (if x < 419 then 378 else 0)) else (if x < 422 then (if x < 421 then 521 else 1460) else (if x < 423 then 670 else 129))) else (if x < 428 then (if x < 426 then (if x < 425 then 1014 else 1184) else (if x < 427 then 938 else 602)) else (if x < 430 then (if x < 429 then 195 else 510) else (if x < 431 then 1394 else 1669)))) else (if x < 440 then (if x < 436 then (if x < 434 then (if x < 433 then 140 else 2057) else (if x < 435 then 1968 else 1607)) else (if x < 438 then (if x < 437 then 17 else 1359) else (if x < 439 then 1897 else 186))) else (if x < 444 then (if x < 442 then (if x < 441 then 255 else 1971) else (if x < 443 then 2018 else 436)) else (if x < 446 then (if x < 445 then 818 else 29) else (if x < 447 then 1268 else 1807))))))

def conjugator_forward_448 (x : ℕ) : ℕ :=
  (if x < 480 then (if x < 464 then (if x < 456 then (if x < 452 then (if x < 450 then (if x < 449 then 19 else 474) else (if x < 451 then 1091 else 464)) else (if x < 454 then (if x < 453 then 1990 else 1112) else (if x < 455 then 2 else 1977))) else (if x < 460 then (if x < 458 then (if x < 457 then 691 else 1506) else (if x < 459 then 808 else 643)) else (if x < 462 then (if x < 461 then 1917 else 632) else (if x < 463 then 1790 else 1196)))) else (if x < 472 then (if x < 468 then (if x < 466 then (if x < 465 then 1417 else 974) else (if x < 467 then 248 else 476)) else (if x < 470 then (if x < 469 then 1504 else 1715) else (if x < 471 then 1594 else 315))) else (if x < 476 then (if x < 474 then (if x < 473 then 678 else 741) else (if x < 475 then 1514 else 320)) else (if x < 478 then (if x < 477 then 571 else 339) else (if x < 479 then 1487 else 708))))) else (if x < 496 then (if x < 488 then (if x < 484 then (if x < 482 then (if x < 481 then 204 else 1495) else (if x < 483 then 1918 else 1475)) else (if x < 486 then (if x < 485 then 1556 else 264) else (if x < 487 then 1955 else 1777))) else (if x < 492 then (if x < 490 then (if x < 489 then 1414 else 1746) else (if x < 491 then 1785 else 183)) else (if x < 494 then (if x < 493 then 1367 else 2001) else (if x < 495 then 613 else 120)))) else (if x < 504 then (if x < 500 then (if x < 498 then (if x < 497 then 1344 else 182) else (if x < 499 then 1600 else 1493)) else (if x < 502 then (if x < 501 then 1538 else 422) else (if x < 503 then 1550 else 1569))) else (if x < 508 then (if x < 506 then (if x < 505 then 302 else 540) else (if x < 507 then 181 else 951)) else (if x < 510 then (if x < 509 then 710 else 1627) else (if x < 511 then 5 else 1201))))))

def conjugator_forward_512 (x : ℕ) : ℕ :=
  (if x < 544 then (if x < 528 then (if x < 520 then (if x < 516 then (if x < 514 then (if x < 513 then 1185 else 1383) else (if x < 515 then 1658 else 1074)) else (if x < 518 then (if x < 517 then 1142 else 542) else (if x < 519 then 597 else 1005))) else (if x < 524 then (if x < 522 then (if x < 521 then 1698 else 1080) else (if x < 523 then 1273 else 1860)) else (if x < 526 then (if x < 525 then 423 else 12) else (if x < 527 then 2019 else 443)))) else (if x < 536 then (if x < 532 then (if x < 530 then (if x < 529 then 32 else 149) else (if x < 531 then 560 else 42)) else (if x < 534 then (if x < 533 then 1902 else 918) else (if x < 535 then 891 else 1374))) else (if x < 540 then (if x < 538 then (if x < 537 then 1655 else 912) else (if x < 539 then 1945 else 216)) else (if x < 542 then (if x < 541 then 1628 else 1298) else (if x < 543 then 642 else 495))))) else (if x < 560 then (if x < 552 then (if x < 548 then (if x < 546 then (if x < 545 then 864 else 1949) else (if x < 547 then 465 else 704)) else (if x < 550 then (if x < 549 then 158 else 1585) else (if x < 551 then 1708 else 482))) else (if x < 556 then (if x < 554 then (if x < 553 then 1464 else 217) else (if x < 555 then 878 else 585)) else (if x < 558 then (if x < 557 then 743 else 415) else (if x < 559 then 810 else 1276)))) else (if x < 568 then (if x < 564 then (if x < 562 then (if x < 561 then 608 else 1615) else (if x < 563 then 1323 else 616)) else (if x < 566 then (if x < 565 then 382 else 1281) else (if x < 567 then 1477 else 1702))) else (if x < 572 then (if x < 570 then (if x < 569 then 1127 else 942) else (if x < 571 then 1795 else 187)) else (if x < 574 then (if x < 573 then 536 else 94) else (if x < 575 then 2045 else 717))))))

def conjugator_forward_576 (x : ℕ) : ℕ :=
  (if x < 608 then (if x < 592 then (if x < 584 then (if x < 580 then (if x < 578 then (if x < 577 then 1012 else 979) else (if x < 579 then 796 else 850)) else (if x < 582 then (if x < 581 then 599 else 1153) else (if x < 583 then 1433 else 2015))) else (if x < 588 then (if x < 586 then (if x < 585 then 1045 else 1331) else (if x < 587 then 894 else 1921)) else (if x < 590 then (if x < 589 then 623 else 914) else (if x < 591 then 1540 else 1291)))) else (if x < 600 then (if x < 596 then (if x < 594 then (if x < 593 then 1793 else 1384) else (if x < 595 then 1980 else 224)) else (if x < 598 then (if x < 597 then 1731 else 180) else (if x < 599 then 408 else 229))) else (if x < 604 then (if x < 602 then (if x < 601 then 920 else 351) else (if x < 603 then 1166 else 101)) else (if x < 606 then (if x < 605 then 31 else 215) else (if x < 607 then 1188 else 1617))))) else (if x < 624 then (if x < 616 then (if x < 612 then (if x < 610 then (if x < 609 then 946 else 930) else (if x < 611 then 692 else 1457)) else (if x < 614 then (if x < 613 then 781 else 1834) else (if x < 615 then 1788 else 780))) else (if x < 620 then (if x < 618 then (if x < 617 then 1928 else 625) else (if x < 619 then 1295 else 352)) else (if x < 622 then (if x < 621 then 136 else 842) else (if x < 623 then 1844 else 1161)))) else (if x < 632 then (if x < 628 then (if x < 626 then (if x < 625 then 572 else 1173) else (if x < 627 then 1306 else 694)) else (if x < 630 then (if x < 629 then 497 else 1097) else (if x < 631 then 1353 else 1418))) else (if x < 636 then (if x < 634 then (if x < 633 then 1889 else 1939) else (if x < 635 then 1541 else 1721)) else (if x < 638 then (if x < 637 then 1194 else 445) else (if x < 639 then 1924 else 1527))))))

def conjugator_forward_640 (x : ℕ) : ℕ :=
  (if x < 672 then (if x < 656 then (if x < 648 then (if x < 644 then (if x < 642 then (if x < 641 then 1133 else 228) else (if x < 643 then 250 else 252)) else (if x < 646 then (if x < 645 then 1404 else 504) else (if x < 647 then 732 else 1723))) else (if x < 652 then (if x < 650 then (if x < 649 then 582 else 718) else (if x < 651 then 1703 else 1922)) else (if x < 654 then (if x < 653 then 518 else 1494) else (if x < 655 then 1577 else 782)))) else (if x < 664 then (if x < 660 then (if x < 658 then (if x < 657 then 401 else 1261) else (if x < 659 then 590 else 1681)) else (if x < 662 then (if x < 661 then 402 else 1985) else (if x < 663 then 60 else 1661))) else (if x < 668 then (if x < 666 then (if x < 665 then 294 else 161) else (if x < 667 then 1126 else 322)) else (if x < 670 then (if x < 669 then 1614 else 1650) else (if x < 671 then 595 else 2025))))) else (if x < 688 then (if x < 680 then (if x < 676 then (if x < 674 then (if x < 673 then 793 else 763) else (if x < 675 then 922 else 361)) else (if x < 678 then (if x < 677 then 2039 else 1386) else (if x < 679 then 880 else 505))) else (if x < 684 then (if x < 682 then (if x < 681 then 1599 else 1635) else (if x < 683 then 637 else 81)) else (if x < 686 then (if x < 685 then 509 else 144) else (if x < 687 then 89 else 126)))) else (if x < 696 then (if x < 692 then (if x < 690 then (if x < 689 then 848 else 1820) else (if x < 691 then 997 else 1948)) else (if x < 694 then (if x < 693 then 759 else 530) else (if x < 695 then 1982 else 730))) else (if x < 700 then (if x < 698 then (if x < 697 then 1919 else 477) else (if x < 699 then 1500 else 1335)) else (if x < 702 then (if x < 701 then 1940 else 1536) else (if x < 703 then 210 else 1381))))))

def conjugator_forward_704 (x : ℕ) : ℕ :=
  (if x < 736 then (if x < 720 then (if x < 712 then (if x < 708 then (if x < 706 then (if x < 705 then 1736 else 1490) else (if x < 707 then 1177 else 1284)) else (if x < 710 then (if x < 709 then 323 else 816) else (if x < 711 then 1686 else 98))) else (if x < 716 then (if x < 714 then (if x < 713 then 1542 else 1653) else (if x < 715 then 239 else 1255)) else (if x < 718 then (if x < 717 then 1174 else 1454) else (if x < 719 then 1277 else 729)))) else (if x < 728 then (if x < 724 then (if x < 722 then (if x < 721 then 638 else 1244) else (if x < 723 then 944 else 1598)) else (if x < 726 then (if x < 725 then 1678 else 1440) else (if x < 727 then 1086 else 1800))) else (if x < 732 then (if x < 730 then (if x < 729 then 1823 else 1642) else (if x < 731 then 1935 else 125)) else (if x < 734 then (if x < 733 then 1096 else 242) else (if x < 735 then 1083 else 1735))))) else (if x < 752 then (if x < 744 then (if x < 740 then (if x < 738 then (if x < 737 then 802 else 1192) else (if x < 739 then 1509 else 1516)) else (if x < 742 then (if x < 741 then 1346 else 57) else (if x < 743 then 2022 else 1117))) else (if x < 748 then (if x < 746 then (if x < 745 then 566 else 37) else (if x < 747 then 1149 else 16)) else (if x < 750 then (if x < 749 then 1366 else 1685) else (if x < 751 then 723 else 644)))) else (if x < 760 then (if x < 756 then (if x < 754 then (if x < 753 then 887 else 150) else (if x < 755 then 1401 else 580)) else (if x < 758 then (if x < 757 then 1051 else 1164) else (if x < 759 then 645 else 437))) else (if x < 764 then (if x < 762 then (if x < 761 then 1310 else 1154) else (if x < 763 then 1308 else 1850)) else (if x < 766 then (if x < 765 then 1531 else 410) else (if x < 767 then 821 else 762))))))

def conjugator_forward_768 (x : ℕ) : ℕ :=
  (if x < 800 then (if x < 784 then (if x < 776 then (if x < 772 then (if x < 770 then (if x < 769 then 468 else 583) else (if x < 771 then 852 else 105)) else (if x < 774 then (if x < 773 then 332 else 1466) else (if x < 775 then 1583 else 711))) else (if x < 780 then (if x < 778 then (if x < 777 then 1727 else 336) else (if x < 779 then 915 else 854)) else (if x < 782 then (if x < 781 then 874 else 1373) else (if x < 783 then 1740 else 1622)))) else (if x < 792 then (if x < 788 then (if x < 786 then (if x < 785 then 2032 else 2052) else (if x < 787 then 1770 else 404)) else (if x < 790 then (if x < 789 then 153 else 444) else (if x < 791 then 1349 else 141))) else (if x < 796 then (if x < 794 then (if x < 793 then 1817 else 1969) else (if x < 795 then 636 else 1603)) else (if x < 798 then (if x < 797 then 709 else 686) else (if x < 799 then 237 else 1030))))) else (if x < 816 then (if x < 808 then (if x < 804 then (if x < 802 then (if x < 801 then 73 else 1218) else (if x < 803 then 1481 else 528)) else (if x < 806 then (if x < 805 then 240 else 1779) else (if x < 807 then 1970 else 1322))) else (if x < 812 then (if x < 810 then (if x < 809 then 220 else 1354) else (if x < 811 then 43 else 1952)) else (if x < 814 then (if x < 813 then 1430 else 959) else (if x < 815 then 1189 else 1520)))) else (if x < 824 then (if x < 820 then (if x < 818 then (if x < 817 then 1421 else 355) else (if x < 819 then 288 else 1238)) else (if x < 822 then (if x < 821 then 1513 else 1056) else (if x < 823 then 1085 else 906))) else (if x < 828 then (if x < 826 then (if x < 825 then 913 else 151) else (if x < 827 then 1908 else 1826)) else (if x < 830 then (if x < 829 then 124 else 685) else (if x < 831 then 38 else 522))))))

def conjugator_forward_832 (x : ℕ) : ℕ :=
  (if x < 864 then (if x < 848 then (if x < 840 then (if x < 836 then (if x < 834 then (if x < 833 then 1722 else 1903) else (if x < 835 then 1757 else 23)) else (if x < 838 then (if x < 837 then 299 else 46) else (if x < 839 then 886 else 1742))) else (if x < 844 then (if x < 842 then (if x < 841 then 1618 else 317) else (if x < 843 then 633 else 624)) else (if x < 846 then (if x < 845 then 1831 else 112) else (if x < 847 then 1048 else 2049)))) else (if x < 856 then (if x < 852 then (if x < 850 then (if x < 849 then 1534 else 1995) else (if x < 851 then 266 else 1410)) else (if x < 854 then (if x < 853 then 1626 else 993) else (if x < 855 then 110 else 574))) else (if x < 860 then (if x < 858 then (if x < 857 then 1387 else 1437) else (if x < 859 then 1956 else 988)) else (if x < 862 then (if x < 861 then 113 else 35) else (if x < 863 then 775 else 318))))) else (if x < 880 then (if x < 872 then (if x < 868 then (if x < 866 then (if x < 865 then 725 else 523) else (if x < 867 then 364 else 851)) else (if x < 870 then (if x < 869 then 916 else 909) else (if x < 871 then 980 else 1317))) else (if x < 876 then (if x < 874 then (if x < 873 then 952 else 1289) else (if x < 875 then 1720 else 1543)) else (if x < 878 then (if x < 877 then 1851 else 748) else (if x < 879 then 1691 else 581)))) else (if x < 888 then (if x < 884 then (if x < 882 then (if x < 881 then 63 else 454) else (if x < 883 then 990 else 1448)) else (if x < 886 then (if x < 885 then 225 else 400) else (if x < 887 then 982 else 155))) else (if x < 892 then (if x < 890 then (if x < 889 then 1405 else 85) else (if x < 891 then 1419 else 1492)) else (if x < 894 then (if x < 893 then 834 else 618) else (if x < 895 then 1833 else 459))))))

def conjugator_forward_896 (x : ℕ) : ℕ :=
  (if x < 928 then (if x < 912 then (if x < 904 then (if x < 900 then (if x < 898 then (if x < 897 then 1640 else 1304) else (if x < 899 then 664 else 1959)) else (if x < 902 then (if x < 901 then 2013 else 1157) else (if x < 903 then 751 else 1805))) else (if x < 908 then (if x < 906 then (if x < 905 then 1682 else 896) else (if x < 907 then 1620 else 279)) else (if x < 910 then (if x < 909 then 515 else 1872) else (if x < 911 then 1954 else 265)))) else (if x < 920 then (if x < 916 then (if x < 914 then (if x < 913 then 1143 else 486) else (if x < 915 then 1962 else 199)) else (if x < 918 then (if x < 917 then 1863 else 1082) else (if x < 919 then 11 else 800))) else (if x < 924 then (if x < 922 then (if x < 921 then 1003 else 345) else (if x < 923 then 1771 else 261)) else (if x < 926 then (if x < 925 then 1630 else 1870) else (if x < 927 then 1496 else 1693))))) else (if x < 944 then (if x < 936 then (if x < 932 then (if x < 930 then (if x < 929 then 1683 else 247) else (if x < 931 then 1313 else 87)) else (if x < 934 then (if x < 933 then 1689 else 681) else (if x < 935 then 453 else 705))) else (if x < 940 then (if x < 938 then (if x < 937 then 905 else 106) else (if x < 939 then 308 else 1100)) else (if x < 942 then (if x < 941 then 1026 else 1) else (if x < 943 then 72 else 1282)))) else (if x < 952 then (if x < 948 then (if x < 946 then (if x < 945 then 1484 else 1094) else (if x < 947 then 1920 else 981)) else (if x < 950 then (if x < 949 then 1361 else 235) else (if x < 951 then 1856 else 695))) else (if x < 956 then (if x < 954 then (if x < 953 then 1835 else 753) else (if x < 955 then 1395 else 499)) else (if x < 958 then (if x < 957 then 471 else 1798) else (if x < 959 then 598 else 593))))))

def conjugator_forward_960 (x : ℕ) : ℕ :=
  (if x < 992 then (if x < 976 then (if x < 968 then (if x < 964 then (if x < 962 then (if x < 961 then 646 else 1099) else (if x < 963 then 953 else 673)) else (if x < 966 then (if x < 965 then 1167 else 500) else (if x < 967 then 1445 else 1217))) else (if x < 972 then (if x < 970 then (if x < 969 then 193 else 1687) else (if x < 971 then 1868 else 1462)) else (if x < 974 then (if x < 973 then 1467 else 1811) else (if x < 975 then 379 else 1624)))) else (if x < 984 then (if x < 980 then (if x < 978 then (if x < 977 then 604 else 742) else (if x < 979 then 596 else 1329)) else (if x < 982 then (if x < 981 then 1933 else 1202) else (if x < 983 then 746 else 1141))) else (if x < 988 then (if x < 986 then (if x < 985 then 448 else 1957) else (if x < 987 then 1436 else 519)) else (if x < 990 then (if x < 989 then 1644 else 735) else (if x < 991 then 8 else 1019))))) else (if x < 1008 then (if x < 1000 then (if x < 996 then (if x < 994 then (if x < 993 then 937 else 1906) else (if x < 995 then 737 else 1625)) else (if x < 998 then (if x < 997 then 75 else 533) else (if x < 999 then 847 else 1076))) else (if x < 1004 then (if x < 1002 then (if x < 1001 then 1709 else 868) else (if x < 1003 then 594 else 634)) else (if x < 1006 then (if x < 1005 then 557 else 1107) else (if x < 1007 then 1305 else 903)))) else (if x < 1016 then (if x < 1012 then (if x < 1010 then (if x < 1009 then 1791 else 1634) else (if x < 1011 then 396 else 385)) else (if x < 1014 then (if x < 1013 then 62 else 1079) else (if x < 1015 then 1674 else 925))) else (if x < 1020 then (if x < 1018 then (if x < 1017 then 576 else 90) else (if x < 1019 then 1480 else 1575)) else (if x < 1022 then (if x < 1021 then 1429 else 21) else (if x < 1023 then 1162 else 935))))))

def conjugator_forward_1024 (x : ℕ) : ℕ :=
  (if x < 1056 then (if x < 1040 then (if x < 1032 then (if x < 1028 then (if x < 1026 then (if x < 1025 then 222 else 462) else (if x < 1027 then 1796 else 2000)) else (if x < 1030 then (if x < 1029 then 1778 else 888) else (if x < 1031 then 1008 else 156))) else (if x < 1036 then (if x < 1034 then (if x < 1033 then 1604 else 561) else (if x < 1035 then 74 else 82)) else (if x < 1038 then (if x < 1037 then 1602 else 53) else (if x < 1039 then 40 else 1783)))) else (if x < 1048 then (if x < 1044 then (if x < 1042 then (if x < 1041 then 1526 else 1832) else (if x < 1043 then 1044 else 1608)) else (if x < 1046 then (if x < 1045 then 950 else 1623) else (if x < 1047 then 1176 else 1043))) else (if x < 1052 then (if x < 1050 then (if x < 1049 then 1925 else 390) else (if x < 1051 then 969 else 55)) else (if x < 1054 then (if x < 1053 then 790 else 1299) else (if x < 1055 then 1824 else 117))))) else (if x < 1072 then (if x < 1064 then (if x < 1060 then (if x < 1058 then (if x < 1057 then 1768 else 1848) else (if x < 1059 then 267 else 1320)) else (if x < 1062 then (if x < 1061 then 619 else 1075) else (if x < 1063 then 1802 else 1638))) else (if x < 1068 then (if x < 1066 then (if x < 1065 then 1247 else 658) else (if x < 1067 then 1227 else 2012)) else (if x < 1070 then (if x < 1069 then 1215 else 765) else (if x < 1071 then 1996 else 1659)))) else (if x < 1080 then (if x < 1076 then (if x < 1074 then (if x < 1073 then 207 else 831) else (if x < 1075 then 814 else 376)) else (if x < 1078 then (if x < 1077 then 747 else 588) else (if x < 1079 then 690 else 627))) else (if x < 1084 then (if x < 1082 then (if x < 1081 then 1198 else 1562) else (if x < 1083 then 96 else 1907)) else (if x < 1086 then (if x < 1085 then 554 else 1378) else (if x < 1087 then 1537 else 677))))))

def conjugator_forward_1088 (x : ℕ) : ℕ :=
  (if x < 1120 then (if x < 1104 then (if x < 1096 then (if x < 1092 then (if x < 1090 then (if x < 1089 then 300 else 615) else (if x < 1091 then 206 else 1563)) else (if x < 1094 then (if x < 1093 then 2037 else 826) else (if x < 1095 then 660 else 245))) else (if x < 1100 then (if x < 1098 then (if x < 1097 then 1392 else 164) else (if x < 1099 then 1328 else 936)) else (if x < 1102 then (if x < 1101 then 168 else 1840) else (if x < 1103 then 95 else 562)))) else (if x < 1112 then (if x < 1108 then (if x < 1106 then (if x < 1105 then 147 else 189) else (if x < 1107 then 1183 else 1169)) else (if x < 1110 then (if x < 1109 then 1901 else 1546) else (if x < 1111 then 1717 else 1287))) else (if x < 1116 then (if x < 1114 then (if x < 1113 then 1533 else 1836) else (if x < 1115 then 1973 else 589)) else (if x < 1118 then (if x < 1117 then 1590 else 1773) else (if x < 1119 then 269 else 194))))) else (if x < 1136 then (if x < 1128 then (if x < 1124 then (if x < 1122 then (if x < 1121 then 1047 else 1131) else (if x < 1123 then 135 else 2007)) else (if x < 1126 then (if x < 1125 then 2002 else 321) else (if x < 1127 then 683 else 722))) else (if x < 1132 then (if x < 1130 then (if x < 1129 then 388 else 348) else (if x < 1131 then 1022 else 290)) else (if x < 1134 then (if x < 1133 then 578 else 1724) else (if x < 1135 then 413 else 2028)))) else (if x < 1144 then (if x < 1140 then (if x < 1138 then (if x < 1137 then 843 else 803) else (if x < 1139 then 2011 else 1943)) else (if x < 1142 then (if x < 1141 then 693 else 209) else (if x < 1143 then 178 else 550))) else (if x < 1148 then (if x < 1146 then (if x < 1145 then 22 else 1243) else (if x < 1147 then 1426 else 706)) else (if x < 1150 then (if x < 1149 then 146 else 198) else (if x < 1151 then 277 else 1482))))))

def conjugator_forward_1152 (x : ℕ) : ℕ :=
  (if x < 1184 then (if x < 1168 then (if x < 1160 then (if x < 1156 then (if x < 1154 then (if x < 1153 then 797 else 121) else (if x < 1155 then 466 else 680)) else (if x < 1158 then (if x < 1157 then 1549 else 948) else (if x < 1159 then 132 else 1989))) else (if x < 1164 then (if x < 1162 then (if x < 1161 then 1438 else 1878) else (if x < 1163 then 565 else 2050)) else (if x < 1166 then (if x < 1165 then 655 else 1558) else (if x < 1167 then 1999 else 1794)))) else (if x < 1176 then (if x < 1172 then (if x < 1170 then (if x < 1169 then 1465 else 384) else (if x < 1171 then 1941 else 507)) else (if x < 1174 then (if x < 1173 then 787 else 1780) else (if x < 1175 then 107 else 1283))) else (if x < 1180 then (if x < 1178 then (if x < 1177 then 1899 else 1106) else (if x < 1179 then 1580 else 458)) else (if x < 1182 then (if x < 1181 then 1120 else 845) else (if x < 1183 then 1748 else 661))))) else (if x < 1200 then (if x < 1192 then (if x < 1188 then (if x < 1186 then (if x < 1185 then 1637 else 1738) else (if x < 1187 then 1115 else 1321)) else (if x < 1190 then (if x < 1189 then 1508 else 1975) else (if x < 1191 then 649 else 525))) else (if x < 1196 then (if x < 1194 then (if x < 1193 then 1447 else 286) else (if x < 1195 then 1645 else 1248)) else (if x < 1198 then (if x < 1197 then 1869 else 159) else (if x < 1199 then 1140 else 855)))) else (if x < 1208 then (if x < 1204 then (if x < 1202 then (if x < 1201 then 1751 else 1375) else (if x < 1203 then 592 else 1885)) else (if x < 1206 then (if x < 1205 then 1882 else 461) else (if x < 1207 then 173 else 65))) else (if x < 1212 then (if x < 1210 then (if x < 1209 then 610 else 357) else (if x < 1211 then 1799 else 1036)) else (if x < 1214 then (if x < 1213 then 1873 else 1219) else (if x < 1215 then 626 else 1181))))))

def conjugator_forward_1216 (x : ℕ) : ℕ :=
  (if x < 1248 then (if x < 1232 then (if x < 1224 then (if x < 1220 then (if x < 1218 then (if x < 1217 then 162 else 429) else (if x < 1219 then 1264 else 1435)) else (if x < 1222 then (if x < 1221 then 287 else 1964) else (if x < 1223 then 383 else 1113))) else (if x < 1228 then (if x < 1226 then (if x < 1225 then 844 else 734) else (if x < 1227 then 1730 else 1114)) else (if x < 1230 then (if x < 1229 then 1884 else 758) else (if x < 1231 then 2004 else 1707)))) else (if x < 1240 then (if x < 1236 then (if x < 1234 then (if x < 1233 then 142 else 1204) else (if x < 1235 then 934 else 1316)) else (if x < 1238 then (if x < 1237 then 553 else 777) else (if x < 1239 then 344 else 1648))) else (if x < 1244 then (if x < 1242 then (if x < 1241 then 839 else 289) else (if x < 1243 then 1451 else 494)) else (if x < 1246 then (if x < 1245 then 1352 else 1412) else (if x < 1247 then 1551 else 1485))))) else (if x < 1264 then (if x < 1256 then (if x < 1252 then (if x < 1250 then (if x < 1249 then 211 else 601) else (if x < 1251 then 1263 else 1397)) else (if x < 1254 then (if x < 1253 then 1733 else 1428) else (if x < 1255 then 1267 else 103))) else (if x < 1260 then (if x < 1258 then (if x < 1257 then 418 else 2005) else (if x < 1259 then 766 else 2020)) else (if x < 1262 then (if x < 1261 then 1672 else 1522) else (if x < 1263 then 1330 else 1705)))) else (if x < 1272 then (if x < 1268 then (if x < 1266 then (if x < 1265 then 1937 else 67) else (if x < 1267 then 1258 else 666)) else (if x < 1270 then (if x < 1269 then 1147 else 139) else (if x < 1271 then 1841 else 1358))) else (if x < 1276 then (if x < 1274 then (if x < 1273 then 811 else 137) else (if x < 1275 then 1175 else 1951)) else (if x < 1278 then (if x < 1277 then 1524 else 56) else (if x < 1279 then 20 else 41))))))

def conjugator_forward_1280 (x : ℕ) : ℕ :=
  (if x < 1312 then (if x < 1296 then (if x < 1288 then (if x < 1284 then (if x < 1282 then (if x < 1281 then 1431 else 798) else (if x < 1283 then 1613 else 908)) else (if x < 1286 then (if x < 1285 then 1561 else 392) else (if x < 1287 then 1910 else 956))) else (if x < 1292 then (if x < 1290 then (if x < 1289 then 1182 else 687) else (if x < 1291 then 190 else 1621)) else (if x < 1294 then (if x < 1293 then 1675 else 799) else (if x < 1295 then 1953 else 160)))) else (if x < 1304 then (if x < 1300 then (if x < 1298 then (if x < 1297 then 86 else 976) else (if x < 1299 then 1597 else 1259)) else (if x < 1302 then (if x < 1301 then 1144 else 1574) else (if x < 1303 then 1979 else 1325))) else (if x < 1308 then (if x < 1306 then (if x < 1305 then 1400 else 1163) else (if x < 1307 then 1510 else 866)) else (if x < 1310 then (if x < 1309 then 329 else 813) else (if x < 1311 then 1341 else 1296))))) else (if x < 1328 then (if x < 1320 then (if x < 1316 then (if x < 1314 then (if x < 1313 then 369 else 2026) else (if x < 1315 then 200 else 391)) else (if x < 1318 then (if x < 1317 then 1007 else 213) else (if x < 1319 then 1458 else 1858))) else (if x < 1324 then (if x < 1322 then (if x < 1321 then 25 else 1071) else (if x < 1323 then 1203 else 1713)) else (if x < 1326 then (if x < 1325 then 1929 else 61) else (if x < 1327 then 233 else 1734)))) else (if x < 1336 then (if x < 1332 then (if x < 1330 then (if x < 1329 then 1409 else 1257) else (if x < 1331 then 1250 else 496)) else (if x < 1334 then (if x < 1333 then 467 else 1946) else (if x < 1335 then 243 else 1105))) else (if x < 1340 then (if x < 1338 then (if x < 1337 then 659 else 1103) else (if x < 1339 then 371 else 450)) else (if x < 1342 then (if x < 1341 then 1553 else 749) else (if x < 1343 then 1649 else 1042))))))

def conjugator_forward_1344 (x : ℕ) : ℕ :=
  (if x < 1376 then (if x < 1360 then (if x < 1352 then (if x < 1348 then (if x < 1346 then (if x < 1345 then 966 else 88) else (if x < 1347 then 131 else 365)) else (if x < 1350 then (if x < 1349 then 881 else 1280) else (if x < 1351 then 1370 else 1633))) else (if x < 1356 then (if x < 1354 then (if x < 1353 then 148 else 1619) else (if x < 1355 then 2036 else 419)) else (if x < 1358 then (if x < 1357 then 792 else 682) else (if x < 1359 then 246 else 342)))) else (if x < 1368 then (if x < 1364 then (if x < 1362 then (if x < 1361 then 343 else 822) else (if x < 1363 then 1818 else 1326)) else (if x < 1366 then (if x < 1365 then 1009 else 1986) else (if x < 1367 then 1616 else 1529))) else (if x < 1372 then (if x < 1370 then (if x < 1369 then 1225 else 1660) else (if x < 1371 then 1391 else 1288)) else (if x < 1374 then (if x < 1373 then 911 else 1829) else (if x < 1375 then 973 else 130))))) else (if x < 1392 then (if x < 1384 then (if x < 1380 then (if x < 1378 then (if x < 1377 then 1564 else 2024) else (if x < 1379 then 1240 else 1876)) else (if x < 1382 then (if x < 1381 then 1146 else 656) else (if x < 1383 then 1582 else 1001))) else (if x < 1388 then (if x < 1386 then (if x < 1385 then 514 else 1379) else (if x < 1387 then 901 else 1459)) else (if x < 1390 then (if x < 1389 then 1212 else 1209) else (if x < 1391 then 26 else 825)))) else (if x < 1400 then (if x < 1396 then (if x < 1394 then (if x < 1393 then 335 else 175) else (if x < 1395 then 1024 else 745)) else (if x < 1398 then (if x < 1397 then 2006 else 1399) else (if x < 1399 then 1423 else 1309))) else (if x < 1404 then (if x < 1402 then (if x < 1401 then 1210 else 1809) else (if x < 1403 then 1376 else 962)) else (if x < 1406 then (if x < 1405 then 478 else 789) else (if x < 1407 then 1676 else 622))))))

def conjugator_forward_1408 (x : ℕ) : ℕ :=
  (if x < 1440 then (if x < 1424 then (if x < 1416 then (if x < 1412 then (if x < 1410 then (if x < 1409 then 1211 else 860) else (if x < 1411 then 1220 else 721)) else (if x < 1414 then (if x < 1413 then 427 else 133) else (if x < 1415 then 1710 else 503))) else (if x < 1420 then (if x < 1418 then (if x < 1417 then 1993 else 1314) else (if x < 1419 then 218 else 1965)) else (if x < 1422 then (if x < 1421 then 1822 else 54) else (if x < 1423 then 1565 else 776)))) else (if x < 1432 then (if x < 1428 then (if x < 1426 then (if x < 1425 then 587 else 1087) else (if x < 1427 then 1806 else 1362)) else (if x < 1430 then (if x < 1429 then 1124 else 1260) else (if x < 1431 then 92 else 303))) else (if x < 1436 then (if x < 1434 then (if x < 1433 then 1688 else 1701) else (if x < 1435 then 177 else 744)) else (if x < 1438 then (if x < 1437 then 1093 else 1845) else (if x < 1439 then 835 else 91))))) else (if x < 1456 then (if x < 1448 then (if x < 1444 then (if x < 1442 then (if x < 1441 then 1994 else 1866) else (if x < 1443 then 1253 else 1663)) else (if x < 1446 then (if x < 1445 then 406 else 386) else (if x < 1447 then 1369 else 1864))) else (if x < 1452 then (if x < 1450 then (if x < 1449 then 1293 else 1972) else (if x < 1451 then 945 else 1632)) else (if x < 1454 then (if x < 1453 then 202 else 1515) else (if x < 1455 then 841 else 885)))) else (if x < 1464 then (if x < 1460 then (if x < 1458 then (if x < 1457 then 1389 else 1230) else (if x < 1459 then 1967 else 45)) else (if x < 1462 then (if x < 1461 then 534 else 830) else (if x < 1463 then 295 else 1013))) else (if x < 1468 then (if x < 1466 then (if x < 1465 then 614 else 1505) else (if x < 1467 then 538 else 253)) else (if x < 1470 then (if x < 1469 then 1923 else 986) else (if x < 1471 then 412 else 1719))))))

def conjugator_forward_1472 (x : ℕ) : ℕ :=
  (if x < 1504 then (if x < 1488 then (if x < 1480 then (if x < 1476 then (if x < 1474 then (if x < 1473 then 1254 else 846) else (if x < 1475 then 926 else 1601)) else (if x < 1478 then (if x < 1477 then 1567 else 1102) else (if x < 1479 then 451 else 1416))) else (if x < 1484 then (if x < 1482 then (if x < 1481 then 363 else 1732) else (if x < 1483 then 965 else 1775)) else (if x < 1486 then (if x < 1485 then 1415 else 1016) else (if x < 1487 then 143 else 1356)))) else (if x < 1496 then (if x < 1492 then (if x < 1490 then (if x < 1489 then 991 else 653) else (if x < 1491 then 1118 else 1512)) else (if x < 1494 then (if x < 1493 then 188 else 326) else (if x < 1495 then 1197 else 272))) else (if x < 1500 then (if x < 1498 then (if x < 1497 then 304 else 870) else (if x < 1499 then 824 else 1363)) else (if x < 1502 then (if x < 1501 then 270 else 2048) else (if x < 1503 then 1468 else 508))))) else (if x < 1520 then (if x < 1512 then (if x < 1508 then (if x < 1506 then (if x < 1505 then 481 else 1020) else (if x < 1507 then 208 else 485)) else (if x < 1510 then (if x < 1509 then 893 else 1178) else (if x < 1511 then 648 else 707))) else (if x < 1516 then (if x < 1514 then (if x < 1513 then 1054 else 1711) else (if x < 1515 then 2041 else 114)) else (if x < 1518 then (if x < 1517 then 1081 else 1229) else (if x < 1519 then 1974 else 1692)))) else (if x < 1528 then (if x < 1524 then (if x < 1522 then (if x < 1521 then 1898 else 405) else (if x < 1523 then 298 else 260)) else (if x < 1526 then (if x < 1525 then 174 else 1725) else (if x < 1527 then 1061 else 1789))) else (if x < 1532 then (if x < 1530 then (if x < 1529 then 1342 else 535) else (if x < 1531 then 761 else 662)) else (if x < 1534 then (if x < 1533 then 929 else 1497) else (if x < 1535 then 720 else 1517))))))

def conjugator_forward_1536 (x : ℕ) : ℕ :=
  (if x < 1568 then (if x < 1552 then (if x < 1544 then (if x < 1540 then (if x < 1538 then (if x < 1537 then 933 else 556) else (if x < 1539 then 1348 else 676)) else (if x < 1542 then (if x < 1541 then 83 else 1461) else (if x < 1543 then 1235 else 558))) else (if x < 1548 then (if x < 1546 then (if x < 1545 then 672 else 840) else (if x < 1547 then 650 else 1947)) else (if x < 1550 then (if x < 1549 then 1871 else 1058) else (if x < 1551 then 1334 else 606)))) else (if x < 1560 then (if x < 1556 then (if x < 1554 then (if x < 1553 then 1938 else 44) else (if x < 1555 then 1782 else 1774)) else (if x < 1558 then (if x < 1557 then 2051 else 1706) else (if x < 1559 then 1471 else 1151))) else (if x < 1564 then (if x < 1562 then (if x < 1561 then 1234 else 1573) else (if x < 1563 then 1548 else 1961)) else (if x < 1566 then (if x < 1565 then 961 else 1364) else (if x < 1567 then 1155 else 1699))))) else (if x < 1584 then (if x < 1576 then (if x < 1572 then (if x < 1570 then (if x < 1569 then 236 else 1242) else (if x < 1571 then 1231 else 2054)) else (if x < 1574 then (if x < 1573 then 1474 else 241) else (if x < 1575 then 493 else 863))) else (if x < 1580 then (if x < 1578 then (if x < 1577 then 795 else 1888) else (if x < 1579 then 739 else 573)) else (if x < 1582 then (if x < 1581 then 1647 else 862) else (if x < 1583 then 93 else 1055)))) else (if x < 1592 then (if x < 1588 then (if x < 1586 then (if x < 1585 then 152 else 1652) else (if x < 1587 then 688 else 1815)) else (if x < 1590 then (if x < 1589 then 768 else 757) else (if x < 1591 then 1767 else 1499))) else (if x < 1596 then (if x < 1594 then (if x < 1593 then 698 else 372) else (if x < 1595 then 1017 else 884)) else (if x < 1598 then (if x < 1597 then 541 else 731) else (if x < 1599 then 374 else 713))))))

def conjugator_forward_1600 (x : ℕ) : ℕ :=
  (if x < 1632 then (if x < 1616 then (if x < 1608 then (if x < 1604 then (if x < 1602 then (if x < 1601 then 171 else 2027) else (if x < 1603 then 2043 else 733)) else (if x < 1606 then (if x < 1605 then 1441 else 1894) else (if x < 1607 then 1654 else 414))) else (if x < 1612 then (if x < 1610 then (if x < 1609 then 338 else 651) else (if x < 1611 then 119 else 1108)) else (if x < 1614 then (if x < 1613 then 1772 else 783) else (if x < 1615 then 1170 else 397)))) else (if x < 1624 then (if x < 1620 then (if x < 1618 then (if x < 1617 then 1158 else 715) else (if x < 1619 then 1145 else 1664)) else (if x < 1622 then (if x < 1621 then 716 else 165) else (if x < 1623 then 1199 else 387))) else (if x < 1628 then (if x < 1626 then (if x < 1625 then 1408 else 319) else (if x < 1627 then 1566 else 1766)) else (if x < 1630 then (if x < 1629 then 815 else 2035) else (if x < 1631 then 883 else 331))))) else (if x < 1648 then (if x < 1640 then (if x < 1636 then (if x < 1634 then (if x < 1633 then 1252 else 967) else (if x < 1635 then 170 else 1651)) else (if x < 1638 then (if x < 1637 then 1443 else 1900) else (if x < 1639 then 511 else 430))) else (if x < 1644 then (if x < 1642 then (if x < 1641 then 1950 else 607) else (if x < 1643 then 349 else 1501)) else (if x < 1646 then (if x < 1645 then 779 else 1302) else (if x < 1647 then 1301 else 1171)))) else (if x < 1656 then (if x < 1652 then (if x < 1650 then (if x < 1649 then 754 else 1849) else (if x < 1651 then 1528 else 873)) else (if x < 1654 then (if x < 1653 then 10 else 30) else (if x < 1655 then 667 else 1883))) else (if x < 1660 then (if x < 1658 then (if x < 1657 then 1327 else 551) else (if x < 1659 then 712 else 489)) else (if x < 1662 then (if x < 1661 then 479 else 832) else (if x < 1663 then 1571 else 97))))))

def conjugator_forward_1664 (x : ℕ) : ℕ :=
  (if x < 1696 then (if x < 1680 then (if x < 1672 then (if x < 1668 then (if x < 1666 then (if x < 1665 then 1046 else 1677) else (if x < 1667 then 1050 else 1755)) else (if x < 1670 then (if x < 1669 then 1966 else 1812) else (if x < 1671 then 631 else 1241))) else (if x < 1676 then (if x < 1674 then (if x < 1673 then 1545 else 449) else (if x < 1675 then 76 else 875)) else (if x < 1678 then (if x < 1677 then 469 else 923) else (if x < 1679 then 472 else 1904)))) else (if x < 1688 then (if x < 1684 then (if x < 1682 then (if x < 1681 then 895 else 502) else (if x < 1683 then 998 else 1991)) else (if x < 1686 then (if x < 1685 then 1029 else 442) else (if x < 1687 then 527 else 313))) else (if x < 1692 then (if x < 1690 then (if x < 1689 then 1324 else 128) else (if x < 1691 then 1275 else 1503)) else (if x < 1694 then (if x < 1693 then 1905 else 801) else (if x < 1695 then 1473 else 1237))))) else (if x < 1712 then (if x < 1704 then (if x < 1700 then (if x < 1698 then (if x < 1697 then 259 else 1859) else (if x < 1699 then 1694 else 539)) else (if x < 1702 then (if x < 1701 then 111 else 769) else (if x < 1703 then 559 else 939))) else (if x < 1708 then (if x < 1706 then (if x < 1705 then 66 else 1750) else (if x < 1707 then 483 else 1763)) else (if x < 1710 then (if x < 1709 then 1065 else 1424) else (if x < 1711 then 325 else 856)))) else (if x < 1720 then (if x < 1716 then (if x < 1714 then (if x < 1713 then 381 else 1568) else (if x < 1715 then 1088 else 1887)) else (if x < 1718 then (if x < 1717 then 2017 else 1011) else (if x < 1719 then 1578 else 1895))) else (if x < 1724 then (if x < 1722 then (if x < 1721 then 1066 else 274) else (if x < 1723 then 1073 else 665)) else (if x < 1726 then (if x < 1725 then 630 else 827) else (if x < 1727 then 740 else 184))))))

def conjugator_forward_1728 (x : ℕ) : ℕ :=
  (if x < 1760 then (if x < 1744 then (if x < 1736 then (if x < 1732 then (if x < 1730 then (if x < 1729 then 1350 else 1656) else (if x < 1731 then 1611 else 24)) else (if x < 1734 then (if x < 1733 then 1449 else 251) else (if x < 1735 then 1610 else 2023))) else (if x < 1740 then (if x < 1738 then (if x < 1737 then 283 else 1816) else (if x < 1739 then 1232 else 368)) else (if x < 1742 then (if x < 1741 then 1187 else 767) else (if x < 1743 then 1804 else 1002)))) else (if x < 1752 then (if x < 1748 then (if x < 1746 then (if x < 1745 then 837 else 603) else (if x < 1747 then 389 else 947)) else (if x < 1750 then (if x < 1749 then 1629 else 1035) else (if x < 1751 then 1891 else 1754))) else (if x < 1756 then (if x < 1754 then (if x < 1753 then 316 else 921) else (if x < 1755 then 872 else 1997)) else (if x < 1758 then (if x < 1757 then 420 else 1262) else (if x < 1759 then 755 else 2030))))) else (if x < 1776 then (if x < 1768 then (if x < 1764 then (if x < 1762 then (if x < 1761 then 879 else 1340) else (if x < 1763 then 1680 else 1078)) else (if x < 1766 then (if x < 1765 then 931 else 555) else (if x < 1767 then 1744 else 1128))) else (if x < 1772 then (if x < 1770 then (if x < 1769 then 2021 else 367) else (if x < 1771 then 1318 else 1639)) else (if x < 1774 then (if x < 1773 then 1668 else 1544) else (if x < 1775 then 196 else 1741)))) else (if x < 1784 then (if x < 1780 then (if x < 1778 then (if x < 1777 then 123 else 1609) else (if x < 1779 then 1148 else 1031)) else (if x < 1782 then (if x < 1781 then 108 else 1393) else (if x < 1783 then 1221 else 724))) else (if x < 1788 then (if x < 1786 then (if x < 1785 then 1122 else 703) else (if x < 1787 then 1838 else 1446)) else (if x < 1790 then (if x < 1789 then 1156 else 394) else (if x < 1791 then 1666 else 2044))))))

def conjugator_forward_1792 (x : ℕ) : ℕ :=
  (if x < 1824 then (if x < 1808 then (if x < 1800 then (if x < 1796 then (if x < 1794 then (if x < 1793 then 1129 else 398) else (if x < 1795 then 2046 else 100)) else (if x < 1798 then (if x < 1797 then 1422 else 456) else (if x < 1799 then 1119 else 1053))) else (if x < 1804 then (if x < 1802 then (if x < 1801 then 719 else 271) else (if x < 1803 then 1136 else 771)) else (if x < 1806 then (if x < 1805 then 1700 else 1251) else (if x < 1807 then 1265 else 1728)))) else (if x < 1816 then (if x < 1812 then (if x < 1810 then (if x < 1809 then 1427 else 1000) else (if x < 1811 then 312 else 1206)) else (if x < 1814 then (if x < 1813 then 1125 else 223) else (if x < 1815 then 1290 else 1934))) else (if x < 1820 then (if x < 1818 then (if x < 1817 then 1274 else 134) else (if x < 1819 then 910 else 1716)) else (if x < 1822 then (if x < 1821 then 1134 else 36) else (if x < 1823 then 978 else 1881))))) else (if x < 1840 then (if x < 1832 then (if x < 1828 then (if x < 1826 then (if x < 1825 then 2033 else 1769) else (if x < 1827 then 1312 else 1926)) else (if x < 1830 then (if x < 1829 then 1006 else 1530) else (if x < 1831 then 1896 else 889))) else (if x < 1836 then (if x < 1834 then (if x < 1833 then 1365 else 1488) else (if x < 1835 then 350 else 1269)) else (if x < 1838 then (if x < 1837 then 48 else 726) else (if x < 1839 then 1060 else 1880)))) else (if x < 1848 then (if x < 1844 then (if x < 1842 then (if x < 1841 then 679 else 1372) else (if x < 1843 then 836 else 809)) else (if x < 1846 then (if x < 1845 then 600 else 426) else (if x < 1847 then 145 else 701))) else (if x < 1852 then (if x < 1850 then (if x < 1849 then 907 else 1792) else (if x < 1851 then 1960 else 256)) else (if x < 1854 then (if x < 1853 then 1963 else 1278) else (if x < 1855 then 552 else 411))))))

def conjugator_forward_1856 (x : ℕ) : ℕ :=
  (if x < 1888 then (if x < 1872 then (if x < 1864 then (if x < 1860 then (if x < 1858 then (if x < 1857 then 79 else 1072) else (if x < 1859 then 49 else 1764)) else (if x < 1862 then (if x < 1861 then 1390 else 2038) else (if x < 1863 then 1179 else 281))) else (if x < 1868 then (if x < 1866 then (if x < 1865 then 257 else 1847) else (if x < 1867 then 1760 else 1837)) else (if x < 1870 then (if x < 1869 then 620 else 1101) else (if x < 1871 then 569 else 205)))) else (if x < 1880 then (if x < 1876 then (if x < 1874 then (if x < 1873 then 927 else 1825) else (if x < 1875 then 1572 else 586)) else (if x < 1878 then (if x < 1877 then 280 else 1502) else (if x < 1879 then 1498 else 657))) else (if x < 1884 then (if x < 1882 then (if x < 1881 then 1743 else 968) else (if x < 1883 then 1523 else 33)) else (if x < 1886 then (if x < 1885 then 285 else 1932) else (if x < 1887 then 1224 else 498))))) else (if x < 1904 then (if x < 1896 then (if x < 1892 then (if x < 1890 then (if x < 1889 then 995 else 641) else (if x < 1891 then 865 else 1292)) else (if x < 1894 then (if x < 1893 then 1984 else 197) else (if x < 1895 then 1388 else 1936))) else (if x < 1900 then (if x < 1898 then (if x < 1897 then 1914 else 1981) else (if x < 1899 then 1521 else 291)) else (if x < 1902 then (if x < 1901 then 380 else 898) else (if x < 1903 then 84 else 1684)))) else (if x < 1912 then (if x < 1908 then (if x < 1906 then (if x < 1905 then 828 else 1813) else (if x < 1907 then 47 else 14)) else (if x < 1910 then (if x < 1909 then 1696 else 526) else (if x < 1911 then 1160 else 532))) else (if x < 1916 then (if x < 1914 then (if x < 1913 then 1808 else 1667) else (if x < 1915 then 1747 else 15)) else (if x < 1918 then (if x < 1917 then 293 else 2009) else (if x < 1919 then 1911 else 501))))))

def conjugator_forward_1920 (x : ℕ) : ℕ :=
  (if x < 1952 then (if x < 1936 then (if x < 1928 then (if x < 1924 then (if x < 1922 then (if x < 1921 then 1038 else 1787) else (if x < 1923 then 1297 else 284)) else (if x < 1926 then (if x < 1925 then 102 else 983) else (if x < 1927 then 1555 else 957))) else (if x < 1932 then (if x < 1930 then (if x < 1929 then 971 else 249) else (if x < 1931 then 647 else 1064)) else (if x < 1934 then (if x < 1933 then 51 else 68) else (if x < 1935 then 964 else 1842)))) else (if x < 1944 then (if x < 1940 then (if x < 1938 then (if x < 1937 then 1539 else 1486) else (if x < 1939 then 1819 else 1472)) else (if x < 1942 then (if x < 1941 then 457 else 307) else (if x < 1943 then 1762 else 172))) else (if x < 1948 then (if x < 1946 then (if x < 1945 then 311 else 127) else (if x < 1947 then 1195 else 1180)) else (if x < 1950 then (if x < 1949 then 575 else 169) else (if x < 1951 then 480 else 1338))))) else (if x < 1968 then (if x < 1960 then (if x < 1956 then (if x < 1954 then (if x < 1953 then 1213 else 1032) else (if x < 1955 then 900 else 1998)) else (if x < 1958 then (if x < 1957 then 1912 else 1307) else (if x < 1959 then 1827 else 1018))) else (if x < 1964 then (if x < 1962 then (if x < 1961 then 460 else 2031) else (if x < 1963 then 1605 else 833)) else (if x < 1966 then (if x < 1965 then 1589 else 1853) else (if x < 1967 then 1704 else 1070)))) else (if x < 1976 then (if x < 1972 then (if x < 1970 then (if x < 1969 then 1470 else 1223) else (if x < 1971 then 1584 else 227)) else (if x < 1974 then (if x < 1973 then 1452 else 1586) else (if x < 1975 then 1068 else 958))) else (if x < 1980 then (if x < 1978 then (if x < 1977 then 1596 else 882) else (if x < 1979 then 1758 else 544)) else (if x < 1982 then (if x < 1981 then 1355 else 1810) else (if x < 1983 then 440 else 2042))))))

def conjugator_forward_1984 (x : ℕ) : ℕ :=
  (if x < 2016 then (if x < 2000 then (if x < 1992 then (if x < 1988 then (if x < 1986 then (if x < 1985 then 621 else 1222) else (if x < 1987 then 902 else 1930)) else (if x < 1990 then (if x < 1989 then 1190 else 567) else (if x < 1991 then 1759 else 463))) else (if x < 1996 then (if x < 1994 then (if x < 1993 then 1315 else 756) else (if x < 1995 then 1403 else 2016)) else (if x < 1998 then (if x < 1997 then 1432 else 1942) else (if x < 1999 then 154 else 1023)))) else (if x < 2008 then (if x < 2004 then (if x < 2002 then (if x < 2001 then 201 else 2053) else (if x < 2003 then 1874 else 1300)) else (if x < 2006 then (if x < 2005 then 2040 else 475) else (if x < 2007 then 268 else 1191))) else (if x < 2012 then (if x < 2010 then (if x < 2009 then 2029 else 399) else (if x < 2011 then 867 else 785)) else (if x < 2014 then (if x < 2013 then 1765 else 877) else (if x < 2015 then 64 else 2010))))) else (if x < 2032 then (if x < 2024 then (if x < 2020 then (if x < 2018 then (if x < 2017 then 1165 else 1150) else (if x < 2019 then 176 else 774)) else (if x < 2022 then (if x < 2021 then 1781 else 579) else (if x < 2023 then 955 else 28))) else (if x < 2028 then (if x < 2026 then (if x < 2025 then 118 else 1491) else (if x < 2027 then 1396 else 275)) else (if x < 2030 then (if x < 2029 then 1236 else 1249) else (if x < 2031 then 617 else 417)))) else (if x < 2040 then (if x < 2036 then (if x < 2034 then (if x < 2033 then 1138 else 163) else (if x < 2035 then 1037 else 1111)) else (if x < 2038 then (if x < 2037 then 1478 else 1439) else (if x < 2039 then 116 else 1444))) else (if x < 2044 then (if x < 2042 then (if x < 2041 then 1854 else 635) else (if x < 2043 then 1695 else 1382)) else (if x < 2046 then (if x < 2045 then 899 else 409) else (if x < 2047 then 714 else 1483))))))

def conjugator_forward_2048 (x : ℕ) : ℕ :=
  (if x < 2053 then (if x < 2050 then (if x < 2049 then 611 else 441) else (if x < 2051 then 1137 else (if x < 2052 then 1592 else 1069))) else (if x < 2055 then (if x < 2054 then 972 else 1130) else (if x < 2056 then 1665 else (if x < 2057 then 39 else 1380))))

def conjugator_forward (v : Fin 2058) : Fin 2058 :=
  let x := v.val
  ⟨((if x < 1024 then (if x < 512 then (if x < 256 then (if x < 128 then (if x < 64 then conjugator_forward_0 x else conjugator_forward_64 x) else (if x < 192 then conjugator_forward_128 x else conjugator_forward_192 x)) else (if x < 384 then (if x < 320 then conjugator_forward_256 x else conjugator_forward_320 x) else (if x < 448 then conjugator_forward_384 x else conjugator_forward_448 x))) else (if x < 768 then (if x < 640 then (if x < 576 then conjugator_forward_512 x else conjugator_forward_576 x) else (if x < 704 then conjugator_forward_640 x else conjugator_forward_704 x)) else (if x < 896 then (if x < 832 then conjugator_forward_768 x else conjugator_forward_832 x) else (if x < 960 then conjugator_forward_896 x else conjugator_forward_960 x)))) else (if x < 1536 then (if x < 1280 then (if x < 1152 then (if x < 1088 then conjugator_forward_1024 x else conjugator_forward_1088 x) else (if x < 1216 then conjugator_forward_1152 x else conjugator_forward_1216 x)) else (if x < 1408 then (if x < 1344 then conjugator_forward_1280 x else conjugator_forward_1344 x) else (if x < 1472 then conjugator_forward_1408 x else conjugator_forward_1472 x))) else (if x < 1792 then (if x < 1664 then (if x < 1600 then conjugator_forward_1536 x else conjugator_forward_1600 x) else (if x < 1728 then conjugator_forward_1664 x else conjugator_forward_1728 x)) else (if x < 1920 then (if x < 1856 then conjugator_forward_1792 x else conjugator_forward_1856 x) else (if x < 1984 then conjugator_forward_1920 x else (if x < 2048 then conjugator_forward_1984 x else conjugator_forward_2048 x))))))) % 2058, Nat.mod_lt _ (by decide)⟩

def conjugator_backward_0 (x : ℕ) : ℕ :=
  (if x < 32 then (if x < 16 then (if x < 8 then (if x < 4 then (if x < 2 then (if x < 1 then 419 else 941) else (if x < 3 then 454 else 140)) else (if x < 6 then (if x < 5 then 402 else 510) else (if x < 7 then 313 else 295))) else (if x < 12 then (if x < 10 then (if x < 9 then 990 else 225) else (if x < 11 then 1652 else 918)) else (if x < 14 then (if x < 13 then 525 else 51) else (if x < 15 then 1907 else 1915)))) else (if x < 24 then (if x < 20 then (if x < 18 then (if x < 17 then 747 else 436) else (if x < 19 then 269 else 448)) else (if x < 22 then (if x < 21 then 1278 else 1021) else (if x < 23 then 1144 else 835))) else (if x < 28 then (if x < 26 then (if x < 25 then 1731 else 1320) else (if x < 27 then 1390 else 375)) else (if x < 30 then (if x < 29 then 2023 else 445) else (if x < 31 then 1653 else 604))))) else (if x < 48 then (if x < 40 then (if x < 36 then (if x < 34 then (if x < 33 then 528 else 1883) else (if x < 35 then 150 else 861)) else (if x < 38 then (if x < 37 then 1821 else 745) else (if x < 39 then 830 else 2056))) else (if x < 44 then (if x < 42 then (if x < 41 then 1038 else 1279) else (if x < 43 then 531 else 810)) else (if x < 46 then (if x < 45 then 1553 else 1459) else (if x < 47 then 837 else 1906)))) else (if x < 56 then (if x < 52 then (if x < 50 then (if x < 49 then 1836 else 1858) else (if x < 51 then 148 else 1932)) else (if x < 54 then (if x < 53 then 294 else 1037) else (if x < 55 then 1421 else 1051))) else (if x < 60 then (if x < 58 then (if x < 57 then 1277 else 741) else (if x < 59 then 205 else 350)) else (if x < 62 then (if x < 61 then 662 else 1325) else (if x < 63 then 1012 else 880))))))

def conjugator_backward_64 (x : ℕ) : ℕ :=
  (if x < 96 then (if x < 80 then (if x < 72 then (if x < 68 then (if x < 66 then (if x < 65 then 2014 else 1207) else (if x < 67 then 1704 else 1265)) else (if x < 70 then (if x < 69 then 1933 else 379) else (if x < 71 then 335 else 397))) else (if x < 76 then (if x < 74 then (if x < 73 then 942 else 800) else (if x < 75 then 1034 else 996)) else (if x < 78 then (if x < 77 then 1674 else 211) else (if x < 79 then 195 else 1856)))) else (if x < 88 then (if x < 84 then (if x < 82 then (if x < 81 then 53 else 683) else (if x < 83 then 1035 else 1540)) else (if x < 86 then (if x < 85 then 1902 else 889) else (if x < 87 then 1296 else 931))) else (if x < 92 then (if x < 90 then (if x < 89 then 1345 else 686) else (if x < 91 then 1017 else 1439)) else (if x < 94 then (if x < 93 then 1430 else 1582) else (if x < 95 then 573 else 1102))))) else (if x < 112 then (if x < 104 then (if x < 100 then (if x < 98 then (if x < 97 then 1082 else 1663) else (if x < 99 then 711 else 353)) else (if x < 102 then (if x < 101 then 1795 else 603) else (if x < 103 then 1924 else 1255))) else (if x < 108 then (if x < 106 then (if x < 105 then 114 else 771) else (if x < 107 then 937 else 1174)) else (if x < 110 then (if x < 109 then 1780 else 109) else (if x < 111 then 854 else 1700)))) else (if x < 120 then (if x < 116 then (if x < 114 then (if x < 113 then 845 else 860) else (if x < 115 then 1515 else 331)) else (if x < 118 then (if x < 117 then 2038 else 1055) else (if x < 119 then 2024 else 1610))) else (if x < 124 then (if x < 122 then (if x < 121 then 495 else 1153) else (if x < 123 then 260 else 1776)) else (if x < 126 then (if x < 125 then 828 else 731) else (if x < 127 then 687 else 1945))))))

def conjugator_backward_128 (x : ℕ) : ℕ :=
  (if x < 160 then (if x < 144 then (if x < 136 then (if x < 132 then (if x < 130 then (if x < 129 then 1689 else 423) else (if x < 131 then 1375 else 1346)) else (if x < 134 then (if x < 133 then 1158 else 1413) else (if x < 135 then 1817 else 1122))) else (if x < 140 then (if x < 138 then (if x < 137 then 620 else 1273) else (if x < 139 then 330 else 1269)) else (if x < 142 then (if x < 141 then 432 else 791) else (if x < 143 then 1232 else 1486)))) else (if x < 152 then (if x < 148 then (if x < 146 then (if x < 145 then 685 else 1846) else (if x < 147 then 1148 else 1104)) else (if x < 150 then (if x < 149 then 1352 else 529) else (if x < 151 then 753 else 825))) else (if x < 156 then (if x < 154 then (if x < 153 then 1584 else 788) else (if x < 155 then 1998 else 887)) else (if x < 158 then (if x < 157 then 1031 else 60) else (if x < 159 then 548 else 1197))))) else (if x < 176 then (if x < 168 then (if x < 164 then (if x < 162 then (if x < 161 then 1295 else 665) else (if x < 163 then 1216 else 2033)) else (if x < 166 then (if x < 165 then 1097 else 1621) else (if x < 167 then 291 else 230))) else (if x < 172 then (if x < 170 then (if x < 169 then 1100 else 1949) else (if x < 171 then 1634 else 1600)) else (if x < 174 then (if x < 173 then 1943 else 1206) else (if x < 175 then 1524 else 1393)))) else (if x < 184 then (if x < 180 then (if x < 178 then (if x < 177 then 2018 else 1434) else (if x < 179 then 1142 else 45)) else (if x < 182 then (if x < 181 then 597 else 506) else (if x < 183 then 497 else 491))) else (if x < 188 then (if x < 186 then (if x < 185 then 1727 else 327) else (if x < 187 then 439 else 571)) else (if x < 190 then (if x < 189 then 1492 else 1105) else (if x < 191 then 1290 else 394))))))

def conjugator_backward_192 (x : ℕ) : ℕ :=
  (if x < 224 then (if x < 208 then (if x < 200 then (if x < 196 then (if x < 194 then (if x < 193 then 317 else 968) else (if x < 195 then 1119 else 428)) else (if x < 198 then (if x < 197 then 1774 else 1893) else (if x < 199 then 1149 else 915))) else (if x < 204 then (if x < 202 then (if x < 201 then 1314 else 2000) else (if x < 203 then 1452 else 117)) else (if x < 206 then (if x < 205 then 480 else 1871) else (if x < 207 then 1090 else 1072)))) else (if x < 216 then (if x < 212 then (if x < 210 then (if x < 209 then 1506 else 1141) else (if x < 211 then 702 else 1248)) else (if x < 214 then (if x < 213 then 395 else 1317) else (if x < 215 then 275 else 605))) else (if x < 220 then (if x < 218 then (if x < 217 then 539 else 553) else (if x < 219 then 1418 else 133)) else (if x < 222 then (if x < 221 then 808 else 399) else (if x < 223 then 1024 else 1813))))) else (if x < 240 then (if x < 232 then (if x < 228 then (if x < 226 then (if x < 225 then 595 else 884) else (if x < 227 then 319 else 1971)) else (if x < 230 then (if x < 229 then 641 else 599) else (if x < 231 then 169 else 199))) else (if x < 236 then (if x < 234 then (if x < 233 then 370 else 1326) else (if x < 235 then 265 else 949)) else (if x < 238 then (if x < 237 then 1568 else 798) else (if x < 239 then 194 else 714)))) else (if x < 248 then (if x < 244 then (if x < 242 then (if x < 241 then 804 else 1573) else (if x < 243 then 733 else 1334)) else (if x < 246 then (if x < 245 then 261 else 1095) else (if x < 247 then 1358 else 929))) else (if x < 252 then (if x < 250 then (if x < 249 then 466 else 1929) else (if x < 251 then 642 else 1733)) else (if x < 254 then (if x < 253 then 643 else 1467) else (if x < 255 then 141 else 440))))))

def conjugator_backward_256 (x : ℕ) : ℕ :=
  (if x < 288 then (if x < 272 then (if x < 264 then (if x < 260 then (if x < 258 then (if x < 257 then 1851 else 1864) else (if x < 259 then 156 else 1696)) else (if x < 262 then (if x < 261 then 1523 else 923) else (if x < 263 then 324 else 198))) else (if x < 268 then (if x < 266 then (if x < 265 then 485 else 911) else (if x < 267 then 850 else 1058)) else (if x < 270 then (if x < 269 then 2006 else 1118) else (if x < 271 then 1500 else 1801)))) else (if x < 280 then (if x < 276 then (if x < 274 then (if x < 273 then 1495 else 216) else (if x < 275 then 1721 else 2027)) else (if x < 278 then (if x < 277 then 0 else 1150) else (if x < 279 then 344 else 907))) else (if x < 284 then (if x < 282 then (if x < 281 then 1876 else 1863) else (if x < 283 then 1 else 1736)) else (if x < 286 then (if x < 285 then 1923 else 1884) else (if x < 287 then 1193 else 1220))))) else (if x < 304 then (if x < 296 then (if x < 292 then (if x < 290 then (if x < 289 then 818 else 1241) else (if x < 291 then 1131 else 1899)) else (if x < 294 then (if x < 293 then 94 else 1916) else (if x < 295 then 664 else 1462))) else (if x < 300 then (if x < 298 then (if x < 297 then 58 else 75) else (if x < 299 then 1522 else 836)) else (if x < 302 then (if x < 301 then 1088 else 162) else (if x < 303 then 504 else 1431)))) else (if x < 312 then (if x < 308 then (if x < 306 then (if x < 305 then 1496 else 346) else (if x < 307 then 175 else 1941)) else (if x < 310 then (if x < 309 then 938 else 185) else (if x < 311 then 374 else 1944))) else (if x < 316 then (if x < 314 then (if x < 313 then 1810 else 1687) else (if x < 315 then 210 else 471)) else (if x < 318 then (if x < 317 then 1752 else 841) else (if x < 319 then 863 else 1625))))))

def conjugator_backward_320 (x : ℕ) : ℕ :=
  (if x < 352 then (if x < 336 then (if x < 328 then (if x < 324 then (if x < 322 then (if x < 321 then 475 else 1125) else (if x < 323 then 667 else 708)) else (if x < 326 then (if x < 325 then 417 else 1710) else (if x < 327 then 1493 else 328))) else (if x < 332 then (if x < 330 then (if x < 329 then 368 else 1308) else (if x < 331 then 81 else 1631)) else (if x < 334 then (if x < 333 then 772 else 27) else (if x < 335 then 189 else 1392)))) else (if x < 344 then (if x < 340 then (if x < 338 then (if x < 337 then 777 else 129) else (if x < 339 then 1608 else 477)) else (if x < 342 then (if x < 341 then 241 else 97) else (if x < 343 then 1359 else 1360))) else (if x < 348 then (if x < 346 then (if x < 345 then 1238 else 921) else (if x < 347 then 95 else 416)) else (if x < 350 then (if x < 349 then 1129 else 1642) else (if x < 351 then 1834 else 601))))) else (if x < 368 then (if x < 360 then (if x < 356 then (if x < 354 then (if x < 353 then 619 else 396) else (if x < 355 then 131 else 817)) else (if x < 358 then (if x < 357 then 283 else 1209) else (if x < 359 then 274 else 415))) else (if x < 364 then (if x < 362 then (if x < 361 then 82 else 675) else (if x < 363 then 113 else 1480)) else (if x < 366 then (if x < 365 then 866 else 1347) else (if x < 367 then 329 else 1769)))) else (if x < 376 then (if x < 372 then (if x < 370 then (if x < 369 then 1739 else 1312) else (if x < 371 then 178 else 1338)) else (if x < 374 then (if x < 373 then 1593 else 101) else (if x < 375 then 1598 else 71))) else (if x < 380 then (if x < 378 then (if x < 377 then 1075 else 39) else (if x < 379 then 418 else 974)) else (if x < 382 then (if x < 381 then 1900 else 1712) else (if x < 383 then 564 else 1222))))))

def conjugator_backward_384 (x : ℕ) : ℕ :=
  (if x < 416 then (if x < 400 then (if x < 392 then (if x < 388 then (if x < 386 then (if x < 385 then 1169 else 1011) else (if x < 387 then 1445 else 1623)) else (if x < 390 then (if x < 389 then 1128 else 1746) else (if x < 391 then 1049 else 1315))) else (if x < 396 then (if x < 394 then (if x < 393 then 1285 else 170) else (if x < 395 then 1789 else 37)) else (if x < 398 then (if x < 397 then 1010 else 1615) else (if x < 399 then 1793 else 2009)))) else (if x < 408 then (if x < 404 then (if x < 402 then (if x < 401 then 885 else 656) else (if x < 403 then 660 else 127)) else (if x < 406 then (if x < 405 then 787 else 1521) else (if x < 407 then 1444 else 258))) else (if x < 412 then (if x < 410 then (if x < 409 then 598 else 2045) else (if x < 411 then 765 else 1855)) else (if x < 414 then (if x < 413 then 1470 else 1134) else (if x < 415 then 1607 else 557))))) else (if x < 432 then (if x < 424 then (if x < 420 then (if x < 418 then (if x < 417 then 62 else 2031) else (if x < 419 then 1256 else 1355)) else (if x < 422 then (if x < 421 then 1756 else 10) else (if x < 423 then 501 else 524))) else (if x < 428 then (if x < 426 then (if x < 425 then 186 else 218) else (if x < 427 then 1845 else 1412)) else (if x < 430 then (if x < 429 then 7 else 1217) else (if x < 431 then 1639 else 349)))) else (if x < 440 then (if x < 436 then (if x < 434 then (if x < 433 then 372 else 360) else (if x < 435 then 119 else 240)) else (if x < 438 then (if x < 437 then 443 else 759) else (if x < 439 then 29 else 121))) else (if x < 444 then (if x < 442 then (if x < 441 then 1982 else 2049) else (if x < 443 then 1685 else 527)) else (if x < 446 then (if x < 445 then 789 else 637) else (if x < 447 then 14 else 236))))))

def conjugator_backward_448 (x : ℕ) : ℕ :=
  (if x < 480 then (if x < 464 then (if x < 456 then (if x < 452 then (if x < 450 then (if x < 449 then 984 else 1673) else (if x < 451 then 1339 else 1478)) else (if x < 454 then (if x < 453 then 61 else 934) else (if x < 455 then 881 else 85))) else (if x < 460 then (if x < 458 then (if x < 457 then 1797 else 1940) else (if x < 459 then 1179 else 895)) else (if x < 462 then (if x < 461 then 1960 else 1205) else (if x < 463 then 1025 else 1991)))) else (if x < 472 then (if x < 468 then (if x < 466 then (if x < 465 then 451 else 546) else (if x < 467 then 1154 else 1332)) else (if x < 470 then (if x < 469 then 768 else 1676) else (if x < 471 then 202 else 956))) else (if x < 476 then (if x < 474 then (if x < 473 then 1678 else 22) else (if x < 475 then 449 else 2005)) else (if x < 478 then (if x < 477 then 467 else 697) else (if x < 479 then 1404 else 1660))))) else (if x < 496 then (if x < 488 then (if x < 484 then (if x < 482 then (if x < 481 then 1950 else 1504) else (if x < 483 then 551 else 1706)) else (if x < 486 then (if x < 485 then 63 else 1507) else (if x < 487 then 913 else 407))) else (if x < 492 then (if x < 490 then (if x < 489 then 386 else 1659) else (if x < 491 then 122 else 256)) else (if x < 494 then (if x < 493 then 128 else 1574) else (if x < 495 then 1243 else 543)))) else (if x < 504 then (if x < 500 then (if x < 498 then (if x < 497 then 1331 else 628) else (if x < 499 then 1887 else 955)) else (if x < 502 then (if x < 501 then 965 else 1919) else (if x < 503 then 1681 else 1415))) else (if x < 508 then (if x < 506 then (if x < 505 then 645 else 679) else (if x < 507 then 365 else 1171)) else (if x < 510 then (if x < 509 then 1503 else 684) else (if x < 511 then 429 else 1638))))))

def conjugator_backward_512 (x : ℕ) : ℕ :=
  (if x < 544 then (if x < 528 then (if x < 520 then (if x < 516 then (if x < 514 then (if x < 513 then 166 else 89) else (if x < 515 then 1384 else 908)) else (if x < 518 then (if x < 517 then 204 else 253) else (if x < 519 then 652 else 987))) else (if x < 524 then (if x < 522 then (if x < 521 then 339 else 420) else (if x < 523 then 831 else 865)) else (if x < 526 then (if x < 525 then 391 else 1191) else (if x < 527 then 1909 else 1686)))) else (if x < 536 then (if x < 532 then (if x < 530 then (if x < 529 then 803 else 49) else (if x < 531 then 693 else 112)) else (if x < 534 then (if x < 533 then 1911 else 997) else (if x < 535 then 1460 else 1529))) else (if x < 540 then (if x < 538 then (if x < 537 then 572 else 326) else (if x < 539 then 1466 else 1699)) else (if x < 542 then (if x < 541 then 505 else 1596) else (if x < 543 then 517 else 207))))) else (if x < 560 then (if x < 552 then (if x < 548 then (if x < 546 then (if x < 545 then 1979 else 103) else (if x < 547 then 33 else 90)) else (if x < 550 then (if x < 549 then 279 else 392) else (if x < 551 then 1143 else 1657))) else (if x < 556 then (if x < 554 then (if x < 553 then 1854 else 1236) else (if x < 555 then 1084 else 1765)) else (if x < 558 then (if x < 557 then 1537 else 1004) else (if x < 559 then 1543 else 1702)))) else (if x < 568 then (if x < 564 then (if x < 562 then (if x < 561 then 530 else 1033) else (if x < 563 then 1103 else 41)) else (if x < 566 then (if x < 565 then 215 else 1162) else (if x < 567 then 744 else 1989))) else (if x < 572 then (if x < 570 then (if x < 569 then 297 else 1870) else (if x < 571 then 376 else 476)) else (if x < 574 then (if x < 573 then 624 else 1579) else (if x < 575 then 855 else 1948))))))

def conjugator_backward_576 (x : ℕ) : ℕ :=
  (if x < 608 then (if x < 592 then (if x < 584 then (if x < 580 then (if x < 578 then (if x < 577 then 1016 else 11) else (if x < 579 then 1132 else 2021)) else (if x < 582 then (if x < 581 then 755 else 879) else (if x < 583 then 648 else 769))) else (if x < 588 then (if x < 586 then (if x < 585 then 285 else 555) else (if x < 587 then 1875 else 1424)) else (if x < 590 then (if x < 589 then 1077 else 1115) else (if x < 591 then 658 else 164)))) else (if x < 600 then (if x < 596 then (if x < 594 then (if x < 593 then 1202 else 959) else (if x < 595 then 1002 else 670)) else (if x < 598 then (if x < 597 then 978 else 518) else (if x < 599 then 958 else 580))) else (if x < 604 then (if x < 602 then (if x < 601 then 1844 else 1249) else (if x < 603 then 427 else 1745)) else (if x < 606 then (if x < 605 then 976 else 191) else (if x < 607 then 1551 else 1641))))) else (if x < 624 then (if x < 616 then (if x < 612 then (if x < 610 then (if x < 609 then 560 else 2) else (if x < 611 then 1208 else 2048)) else (if x < 614 then (if x < 613 then 242 else 494) else (if x < 615 then 1464 else 1089))) else (if x < 620 then (if x < 618 then (if x < 617 then 563 else 2030) else (if x < 619 then 893 else 1060)) else (if x < 622 then (if x < 621 then 1868 else 1984) else (if x < 623 then 1407 else 588)))) else (if x < 632 then (if x < 628 then (if x < 626 then (if x < 625 then 843 else 617) else (if x < 627 then 1214 else 1079)) else (if x < 630 then (if x < 629 then 315 else 373) else (if x < 631 then 1724 else 1670))) else (if x < 636 then (if x < 634 then (if x < 633 then 461 else 842) else (if x < 635 then 1003 else 2041)) else (if x < 638 then (if x < 637 then 794 else 682) else (if x < 639 then 720 else 139))))))

def conjugator_backward_640 (x : ℕ) : ℕ :=
  (if x < 672 then (if x < 656 then (if x < 648 then (if x < 644 then (if x < 642 then (if x < 641 then 142 else 1889) else (if x < 643 then 542 else 459)) else (if x < 646 then (if x < 645 then 751 else 758) else (if x < 647 then 960 else 1930))) else (if x < 652 then (if x < 650 then (if x < 649 then 1510 else 1190) else (if x < 651 then 1546 else 1609)) else (if x < 654 then (if x < 653 then 72 else 1489) else (if x < 655 then 266 else 1164)))) else (if x < 664 then (if x < 660 then (if x < 658 then (if x < 657 then 1381 else 1879) else (if x < 659 then 1065 else 1336)) else (if x < 662 then (if x < 661 then 1094 else 1183) else (if x < 663 then 1531 else 23))) else (if x < 668 then (if x < 666 then (if x < 665 then 898 else 1723) else (if x < 667 then 1267 else 1654)) else (if x < 670 then (if x < 669 then 100 else 153) else (if x < 671 then 422 else 160))))) else (if x < 688 then (if x < 680 then (if x < 676 then (if x < 674 then (if x < 673 then 1544 else 963) else (if x < 675 then 20 else 137)) else (if x < 678 then (if x < 677 then 1539 else 1087) else (if x < 679 then 472 else 1840))) else (if x < 684 then (if x < 682 then (if x < 681 then 1155 else 933) else (if x < 683 then 1357 else 1126)) else (if x < 686 then (if x < 685 then 183 else 829) else (if x < 687 then 797 else 1289)))) else (if x < 696 then (if x < 692 then (if x < 690 then (if x < 689 then 1586 else 305) else (if x < 691 then 1078 else 456)) else (if x < 694 then (if x < 693 then 610 else 1140) else (if x < 695 then 627 else 951))) else (if x < 700 then (if x < 698 then (if x < 697 then 351 else 381) else (if x < 699 then 1592 else 98)) else (if x < 702 then (if x < 701 then 12 else 1847) else (if x < 703 then 134 else 1785))))))

def conjugator_backward_704 (x : ℕ) : ℕ :=
  (if x < 736 then (if x < 720 then (if x < 712 then (if x < 708 then (if x < 706 then (if x < 705 then 547 else 935) else (if x < 707 then 1147 else 1511)) else (if x < 710 then (if x < 709 then 479 else 796) else (if x < 711 then 508 else 775))) else (if x < 716 then (if x < 714 then (if x < 713 then 1658 else 1599) else (if x < 715 then 2046 else 1617)) else (if x < 718 then (if x < 717 then 1620 else 575) else (if x < 719 then 649 else 1800)))) else (if x < 728 then (if x < 724 then (if x < 722 then (if x < 721 then 1534 else 1411) else (if x < 723 then 1127 else 750)) else (if x < 726 then (if x < 725 then 1783 else 864) else (if x < 727 then 1837 else 362))) else (if x < 732 then (if x < 730 then (if x < 729 then 74 else 719) else (if x < 731 then 695 else 1597)) else (if x < 734 then (if x < 733 then 646 else 1603) else (if x < 735 then 1225 else 989))))) else (if x < 752 then (if x < 744 then (if x < 740 then (if x < 738 then (if x < 737 then 356 else 994) else (if x < 739 then 254 else 1578)) else (if x < 742 then (if x < 741 then 1726 else 473) else (if x < 743 then 977 else 556))) else (if x < 748 then (if x < 746 then (if x < 745 then 1435 else 1395) else (if x < 747 then 982 else 1076)) else (if x < 750 then (if x < 749 then 877 else 1341) else (if x < 751 then 411 else 902)))) else (if x < 760 then (if x < 756 then (if x < 754 then (if x < 753 then 406 else 953) else (if x < 755 then 1648 else 1758)) else (if x < 758 then (if x < 757 then 1993 else 1589) else (if x < 759 then 1229 else 692))) else (if x < 764 then (if x < 762 then (if x < 761 then 380 else 1530) else (if x < 763 then 767 else 673)) else (if x < 766 then (if x < 765 then 108 else 1069) else (if x < 767 then 1258 else 1741))))))

def conjugator_backward_768 (x : ℕ) : ℕ :=
  (if x < 800 then (if x < 784 then (if x < 776 then (if x < 772 then (if x < 770 then (if x < 769 then 1588 else 1701) else (if x < 771 then 272 else 1803)) else (if x < 774 then (if x < 773 then 161 else 278) else (if x < 775 then 2019 else 862))) else (if x < 780 then (if x < 778 then (if x < 777 then 1423 else 1237) else (if x < 779 then 118 else 1644)) else (if x < 782 then (if x < 781 then 615 else 612) else (if x < 783 then 655 else 1613)))) else (if x < 792 then (if x < 788 then (if x < 786 then (if x < 785 then 255 else 2011) else (if x < 787 then 220 else 1172)) else (if x < 790 then (if x < 789 then 290 else 1405) else (if x < 791 then 1052 else 299))) else (if x < 796 then (if x < 794 then (if x < 793 then 1356 else 672) else (if x < 795 then 34 else 1576)) else (if x < 798 then (if x < 797 then 578 else 1152) else (if x < 799 then 1281 else 1293))))) else (if x < 816 then (if x < 808 then (if x < 804 then (if x < 802 then (if x < 801 then 919 else 1693) else (if x < 803 then 736 else 1137)) else (if x < 806 then (if x < 805 then 393 else 177) else (if x < 807 then 18 else 400))) else (if x < 812 then (if x < 810 then (if x < 809 then 458 else 1843) else (if x < 811 then 558 else 1272)) else (if x < 814 then (if x < 813 then 182 else 1309) else (if x < 815 then 1074 else 1628)))) else (if x < 824 then (if x < 820 then (if x < 818 then (if x < 817 then 709 else 257) else (if x < 819 then 444 else 387)) else (if x < 822 then (if x < 821 then 32 else 766) else (if x < 823 then 1361 else 304))) else (if x < 828 then (if x < 826 then (if x < 825 then 1498 else 1391) else (if x < 827 then 1093 else 1725)) else (if x < 830 then (if x < 829 then 1904 else 214) else (if x < 831 then 1461 else 1073))))))

def conjugator_backward_832 (x : ℕ) : ℕ :=
  (if x < 864 then (if x < 848 then (if x < 840 then (if x < 836 then (if x < 834 then (if x < 833 then 1661 else 1963) else (if x < 835 then 892 else 1438)) else (if x < 838 then (if x < 837 then 1842 else 1744) else (if x < 839 then 245 else 1240))) else (if x < 844 then (if x < 842 then (if x < 841 then 1545 else 1454) else (if x < 843 then 621 else 1136)) else (if x < 846 then (if x < 845 then 1224 else 1181) else (if x < 847 then 1473 else 998)))) else (if x < 856 then (if x < 852 then (if x < 850 then (if x < 849 then 688 else 155) else (if x < 851 then 579 else 867)) else (if x < 854 then (if x < 853 then 770 else 307) else (if x < 855 then 779 else 1199))) else (if x < 860 then (if x < 858 then (if x < 857 then 1711 else 358) else (if x < 859 then 132 else 388)) else (if x < 862 then (if x < 861 then 1409 else 414) else (if x < 863 then 1581 else 1575))))) else (if x < 880 then (if x < 872 then (if x < 868 then (if x < 866 then (if x < 865 then 544 else 1890) else (if x < 867 then 1307 else 2010)) else (if x < 870 then (if x < 869 then 1001 else 16) else (if x < 871 then 1497 else 348))) else (if x < 876 then (if x < 874 then (if x < 873 then 1754 else 1651) else (if x < 875 then 780 else 1675)) else (if x < 878 then (if x < 877 then 115 else 2013) else (if x < 879 then 554 else 1760)))) else (if x < 888 then (if x < 884 then (if x < 882 then (if x < 881 then 678 else 1348) else (if x < 883 then 1977 else 1630)) else (if x < 886 then (if x < 885 then 1595 else 1455) else (if x < 887 then 838 else 752))) else (if x < 892 then (if x < 890 then (if x < 889 then 1029 else 1831) else (if x < 891 then 264 else 534)) else (if x < 894 then (if x < 893 then 43 else 1508) else (if x < 895 then 586 else 1680))))))

def conjugator_backward_896 (x : ℕ) : ℕ :=
  (if x < 928 then (if x < 912 then (if x < 904 then (if x < 900 then (if x < 898 then (if x < 897 then 905 else 44) else (if x < 899 then 1901 else 2044)) else (if x < 902 then (if x < 901 then 1954 else 1386) else (if x < 903 then 1986 else 1007))) else (if x < 908 then (if x < 906 then (if x < 905 then 262 else 936) else (if x < 907 then 823 else 1848)) else (if x < 910 then (if x < 909 then 1283 else 869) else (if x < 911 then 1818 else 1372)))) else (if x < 920 then (if x < 916 then (if x < 914 then (if x < 913 then 537 else 824) else (if x < 915 then 589 else 778)) else (if x < 918 then (if x < 917 then 868 else 86) else (if x < 919 then 533 else 390))) else (if x < 924 then (if x < 922 then (if x < 921 then 600 else 1753) else (if x < 923 then 674 else 1677)) else (if x < 926 then (if x < 925 then 15 else 1015) else (if x < 927 then 1474 else 1872))))) else (if x < 944 then (if x < 936 then (if x < 932 then (if x < 930 then (if x < 929 then 405 else 1532) else (if x < 931 then 609 else 1764)) else (if x < 934 then (if x < 933 then 159 else 1536) else (if x < 935 then 1234 else 1023))) else (if x < 940 then (if x < 938 then (if x < 937 then 1099 else 992) else (if x < 939 then 426 else 1703)) else (if x < 942 then (if x < 941 then 35 else 223) else (if x < 943 then 569 else 337)))) else (if x < 952 then (if x < 948 then (if x < 946 then (if x < 945 then 722 else 1450) else (if x < 947 then 608 else 1747)) else (if x < 950 then (if x < 949 then 1157 else 138) else (if x < 951 then 1044 else 507))) else (if x < 956 then (if x < 954 then (if x < 953 then 872 else 962) else (if x < 955 then 136 else 2022)) else (if x < 958 then (if x < 957 then 1287 else 1927) else (if x < 959 then 1975 else 813))))))

def conjugator_backward_960 (x : ℕ) : ℕ :=
  (if x < 992 then (if x < 976 then (if x < 968 then (if x < 964 then (if x < 962 then (if x < 961 then 412 else 1564) else (if x < 963 then 1403 else 181)) else (if x < 966 then (if x < 965 then 1934 else 1482) else (if x < 967 then 1344 else 1633))) else (if x < 972 then (if x < 970 then (if x < 969 then 1881 else 1050) else (if x < 971 then 300 else 1928)) else (if x < 974 then (if x < 973 then 2053 else 1374) else (if x < 975 then 465 else 125)))) else (if x < 984 then (if x < 980 then (if x < 978 then (if x < 977 then 1297 else 83) else (if x < 979 then 1822 else 577)) else (if x < 982 then (if x < 981 then 870 else 947) else (if x < 983 then 886 else 1925))) else (if x < 988 then (if x < 986 then (if x < 985 then 146 else 238) else (if x < 987 then 1469 else 165)) else (if x < 990 then (if x < 989 then 859 else 224) else (if x < 991 then 882 else 1488))))) else (if x < 1008 then (if x < 1000 then (if x < 996 then (if x < 994 then (if x < 993 then 56 else 853) else (if x < 995 then 404 else 1888)) else (if x < 998 then (if x < 997 then 251 else 690) else (if x < 999 then 1682 else 197))) else (if x < 1004 then (if x < 1002 then (if x < 1001 then 1809 else 1383) else (if x < 1003 then 1743 else 920)) else (if x < 1006 then (if x < 1005 then 135 else 519) else (if x < 1007 then 1828 else 1316)))) else (if x < 1016 then (if x < 1012 then (if x < 1010 then (if x < 1009 then 1030 else 1364) else (if x < 1011 then 57 else 1717)) else (if x < 1014 then (if x < 1013 then 576 else 1463) else (if x < 1015 then 424 else 193))) else (if x < 1020 then (if x < 1018 then (if x < 1017 then 1485 else 1594) else (if x < 1019 then 1959 else 991)) else (if x < 1022 then (if x < 1021 then 1505 else 69) else (if x < 1023 then 1130 else 1999))))))

def conjugator_backward_1024 (x : ℕ) : ℕ :=
  (if x < 1056 then (if x < 1040 then (if x < 1032 then (if x < 1028 then (if x < 1026 then (if x < 1025 then 1394 else 4) else (if x < 1027 then 940 else 105)) else (if x < 1030 then (if x < 1029 then 378 else 1684) else (if x < 1031 then 799 else 1779))) else (if x < 1036 then (if x < 1034 then (if x < 1033 then 1953 else 263) else (if x < 1035 then 180 else 1749)) else (if x < 1038 then (if x < 1037 then 1211 else 2034) else (if x < 1039 then 1920 else 36)))) else (if x < 1048 then (if x < 1044 then (if x < 1042 then (if x < 1041 then 47 else 314) else (if x < 1043 then 1343 else 1047)) else (if x < 1046 then (if x < 1045 then 1042 else 584) else (if x < 1047 then 1664 else 1120))) else (if x < 1052 then (if x < 1050 then (if x < 1049 then 846 else 78) else (if x < 1051 then 1666 else 756)) else (if x < 1054 then (if x < 1053 then 144 else 1799) else (if x < 1055 then 1512 else 1583))))) else (if x < 1072 then (if x < 1064 then (if x < 1060 then (if x < 1058 then (if x < 1057 then 821 else 281) else (if x < 1059 then 1549 else 13)) else (if x < 1062 then (if x < 1061 then 1838 else 1526) else (if x < 1063 then 21 else 110))) else (if x < 1068 then (if x < 1066 then (if x < 1065 then 1931 else 1708) else (if x < 1067 then 1720 else 65)) else (if x < 1070 then (if x < 1069 then 1974 else 2052) else (if x < 1071 then 1967 else 1321)))) else (if x < 1080 then (if x < 1076 then (if x < 1074 then (if x < 1073 then 1857 else 1722) else (if x < 1075 then 515 else 1061)) else (if x < 1078 then (if x < 1077 then 999 else 352) else (if x < 1079 then 1763 else 1013))) else (if x < 1084 then (if x < 1082 then (if x < 1081 then 521 else 1516) else (if x < 1083 then 917 else 734)) else (if x < 1086 then (if x < 1085 then 233 else 822) else (if x < 1087 then 726 else 1425))))))

def conjugator_backward_1088 (x : ℕ) : ℕ :=
  (if x < 1120 then (if x < 1104 then (if x < 1096 then (if x < 1092 then (if x < 1090 then (if x < 1089 then 1714 else 102) else (if x < 1091 then 42 else 450)) else (if x < 1094 then (if x < 1093 then 212 else 1436) else (if x < 1095 then 945 else 333))) else (if x < 1100 then (if x < 1098 then (if x < 1097 then 732 else 629) else (if x < 1099 then 321 else 961)) else (if x < 1102 then (if x < 1101 then 939 else 1869) else (if x < 1103 then 1477 else 1337)))) else (if x < 1112 then (if x < 1108 then (if x < 1106 then (if x < 1105 then 80 else 1335) else (if x < 1107 then 1177 else 1005)) else (if x < 1110 then (if x < 1109 then 1611 else 88) else (if x < 1111 then 276 else 2035))) else (if x < 1116 then (if x < 1114 then (if x < 1113 then 453 else 1223) else (if x < 1115 then 1227 else 1186)) else (if x < 1118 then (if x < 1117 then 130 else 743) else (if x < 1119 then 1490 else 1798))))) else (if x < 1136 then (if x < 1128 then (if x < 1124 then (if x < 1122 then (if x < 1121 then 1180 else 213) else (if x < 1123 then 1784 else 277)) else (if x < 1126 then (if x < 1125 then 1428 else 1812) else (if x < 1127 then 666 else 568))) else (if x < 1132 then (if x < 1130 then (if x < 1129 then 1767 else 1792) else (if x < 1131 then 2054 else 1121)) else (if x < 1134 then (if x < 1133 then 318 else 640) else (if x < 1135 then 1820 else 237)))) else (if x < 1144 then (if x < 1140 then (if x < 1138 then (if x < 1137 then 1802 else 2050) else (if x < 1139 then 2032 else 26)) else (if x < 1142 then (if x < 1141 then 1198 else 983) else (if x < 1143 then 516 else 912))) else (if x < 1148 then (if x < 1146 then (if x < 1145 then 1300 else 1618) else (if x < 1147 then 1380 else 1268)) else (if x < 1150 then (if x < 1149 then 1778 else 746) else (if x < 1151 then 2017 else 1559))))))

def conjugator_backward_1152 (x : ℕ) : ℕ :=
  (if x < 1184 then (if x < 1168 then (if x < 1160 then (if x < 1156 then (if x < 1154 then (if x < 1153 then 158 else 581) else (if x < 1155 then 761 else 1566)) else (if x < 1158 then (if x < 1157 then 1788 else 901) else (if x < 1159 then 1616 else 366))) else (if x < 1164 then (if x < 1162 then (if x < 1161 then 1910 else 623) else (if x < 1163 then 1022 else 1305)) else (if x < 1166 then (if x < 1165 then 757 else 2016) else (if x < 1167 then 602 else 964)))) else (if x < 1176 then (if x < 1172 then (if x < 1170 then (if x < 1169 then 59 else 1107) else (if x < 1171 then 1614 else 1647)) else (if x < 1174 then (if x < 1173 then 79 else 625) else (if x < 1175 then 716 else 1274))) else (if x < 1180 then (if x < 1178 then (if x < 1177 then 1046 else 706) else (if x < 1179 then 1509 else 1862)) else (if x < 1182 then (if x < 1181 then 1947 else 1215) else (if x < 1183 then 1288 else 1106))))) else (if x < 1200 then (if x < 1192 then (if x < 1188 then (if x < 1186 then (if x < 1185 then 425 else 512) else (if x < 1187 then 280 else 1740)) else (if x < 1190 then (if x < 1189 then 606 else 814) else (if x < 1191 then 1988 else 2007))) else (if x < 1196 then (if x < 1194 then (if x < 1193 then 737 else 9) else (if x < 1195 then 636 else 1946)) else (if x < 1198 then (if x < 1197 then 463 else 1494) else (if x < 1199 then 1080 else 1622)))) else (if x < 1208 then (if x < 1204 then (if x < 1202 then (if x < 1201 then 382 else 511) else (if x < 1203 then 981 else 1322)) else (if x < 1206 then (if x < 1205 then 1233 else 252) else (if x < 1207 then 1811 else 325))) else (if x < 1212 then (if x < 1210 then (if x < 1209 then 334 else 1389) else (if x < 1211 then 1400 else 1408)) else (if x < 1214 then (if x < 1213 then 1388 else 1952) else (if x < 1215 then 287 else 1068))))))

def conjugator_backward_1216 (x : ℕ) : ℕ :=
  (if x < 1248 then (if x < 1232 then (if x < 1224 then (if x < 1220 then (if x < 1218 then (if x < 1217 then 96 else 967) else (if x < 1219 then 801 else 1213)) else (if x < 1222 then (if x < 1221 then 1410 else 1782) else (if x < 1223 then 1985 else 1969))) else (if x < 1228 then (if x < 1226 then (if x < 1225 then 1886 else 1368) else (if x < 1227 then 203 else 1066)) else (if x < 1230 then (if x < 1229 then 403 else 1517) else (if x < 1231 then 1457 else 1570)))) else (if x < 1240 then (if x < 1236 then (if x < 1234 then (if x < 1233 then 1738 else 371) else (if x < 1235 then 1560 else 1542)) else (if x < 1238 then (if x < 1237 then 2028 else 1695) else (if x < 1239 then 819 else 323))) else (if x < 1244 then (if x < 1242 then (if x < 1241 then 1378 else 1671) else (if x < 1243 then 1569 else 1145)) else (if x < 1246 then (if x < 1245 then 721 else 152) else (if x < 1247 then 163 else 1064))))) else (if x < 1264 then (if x < 1256 then (if x < 1252 then (if x < 1250 then (if x < 1249 then 1195 else 2029) else (if x < 1251 then 1330 else 1805)) else (if x < 1254 then (if x < 1253 then 1632 else 1442) else (if x < 1255 then 1472 else 715))) else (if x < 1260 then (if x < 1258 then (if x < 1257 then 243 else 1329) else (if x < 1259 then 1266 else 1299)) else (if x < 1262 then (if x < 1261 then 1429 else 657) else (if x < 1263 then 1757 else 1250)))) else (if x < 1272 then (if x < 1268 then (if x < 1266 then (if x < 1265 then 1218 else 1806) else (if x < 1267 then 226 else 1254)) else (if x < 1270 then (if x < 1269 then 446 else 1835) else (if x < 1271 then 364 else 145))) else (if x < 1276 then (if x < 1274 then (if x < 1273 then 413 else 522) else (if x < 1275 then 1816 else 1690)) else (if x < 1278 then (if x < 1277 then 559 else 718) else (if x < 1279 then 1853 else 73))))))

def conjugator_backward_1280 (x : ℕ) : ℕ :=
  (if x < 1312 then (if x < 1296 then (if x < 1288 then (if x < 1284 then (if x < 1282 then (if x < 1281 then 1349 else 565) else (if x < 1283 then 943 else 1175)) else (if x < 1286 then (if x < 1285 then 707 else 284) else (if x < 1287 then 361 else 1111))) else (if x < 1292 then (if x < 1290 then (if x < 1289 then 1371 else 873) else (if x < 1291 then 1814 else 591)) else (if x < 1294 then (if x < 1293 then 1891 else 1448) else (if x < 1295 then 76 else 618)))) else (if x < 1304 then (if x < 1300 then (if x < 1298 then (if x < 1297 then 1311 else 1922) else (if x < 1299 then 541 else 1053)) else (if x < 1302 then (if x < 1301 then 2003 else 1646) else (if x < 1303 then 1645 else 157))) else (if x < 1308 then (if x < 1306 then (if x < 1305 then 897 else 1006) else (if x < 1307 then 626 else 1957)) else (if x < 1310 then (if x < 1309 then 762 else 1399) else (if x < 1311 then 760 else 332))))) else (if x < 1328 then (if x < 1320 then (if x < 1316 then (if x < 1314 then (if x < 1313 then 1826 else 930) else (if x < 1315 then 1417 else 1992)) else (if x < 1318 then (if x < 1317 then 1235 else 871) else (if x < 1319 then 1770 else 369))) else (if x < 1324 then (if x < 1322 then (if x < 1321 then 1059 else 1187) else (if x < 1323 then 807 else 562)) else (if x < 1326 then (if x < 1325 then 1688 else 1303) else (if x < 1327 then 1363 else 1656)))) else (if x < 1336 then (if x < 1332 then (if x < 1330 then (if x < 1329 then 1098 else 979) else (if x < 1331 then 1262 else 585)) else (if x < 1334 then (if x < 1333 then 309 else 38) else (if x < 1335 then 1550 else 699))) else (if x < 1340 then (if x < 1338 then (if x < 1337 then 19 else 343) else (if x < 1339 then 1951 else 227)) else (if x < 1342 then (if x < 1341 then 1761 else 1310) else (if x < 1343 then 1528 else 355))))))

def conjugator_backward_1344 (x : ℕ) : ℕ :=
  (if x < 1376 then (if x < 1360 then (if x < 1352 then (if x < 1348 then (if x < 1346 then (if x < 1345 then 496 else 84) else (if x < 1347 then 740 else 345)) else (if x < 1350 then (if x < 1349 then 1538 else 790) else (if x < 1351 then 1728 else 200))) else (if x < 1356 then (if x < 1354 then (if x < 1353 then 1244 else 630) else (if x < 1355 then 809 else 1980)) else (if x < 1358 then (if x < 1357 then 1487 else 340) else (if x < 1359 then 1271 else 437)))) else (if x < 1368 then (if x < 1364 then (if x < 1362 then (if x < 1361 then 151 else 948) else (if x < 1363 then 1427 else 1499)) else (if x < 1366 then (if x < 1365 then 1565 else 1832) else (if x < 1367 then 748 else 492))) else (if x < 1372 then (if x < 1370 then (if x < 1369 then 383 else 1446) else (if x < 1371 then 1350 else 92)) else (if x < 1374 then (if x < 1373 then 1841 else 781) else (if x < 1375 then 535 else 1201))))) else (if x < 1392 then (if x < 1384 then (if x < 1380 then (if x < 1378 then (if x < 1377 then 1402 else 398) else (if x < 1379 then 1085 else 1385)) else (if x < 1382 then (if x < 1381 then 2057 else 703) else (if x < 1383 then 2043 else 513))) else (if x < 1388 then (if x < 1386 then (if x < 1385 then 593 else 367) else (if x < 1387 then 677 else 856)) else (if x < 1390 then (if x < 1389 then 1894 else 1456) else (if x < 1391 then 1860 else 1370)))) else (if x < 1400 then (if x < 1396 then (if x < 1394 then (if x < 1393 then 1096 else 1781) else (if x < 1395 then 430 else 954)) else (if x < 1398 then (if x < 1397 then 2026 else 1251) else (if x < 1399 then 126 else 1397))) else (if x < 1404 then (if x < 1402 then (if x < 1401 then 1304 else 754) else (if x < 1403 then 232 else 1994)) else (if x < 1406 then (if x < 1405 then 644 else 888) else (if x < 1407 then 3 else 77))))))

def conjugator_backward_1408 (x : ℕ) : ℕ :=
  (if x < 1440 then (if x < 1424 then (if x < 1416 then (if x < 1412 then (if x < 1410 then (if x < 1409 then 1624 else 1328) else (if x < 1411 then 851 else 149)) else (if x < 1414 then (if x < 1413 then 1245 else 40) else (if x < 1415 then 488 else 1484))) else (if x < 1420 then (if x < 1418 then (if x < 1417 then 1479 else 464) else (if x < 1419 then 631 else 890)) else (if x < 1422 then (if x < 1421 then 282 else 816) else (if x < 1423 then 1796 else 1398)))) else (if x < 1432 then (if x < 1428 then (if x < 1426 then (if x < 1425 then 1709 else 111) else (if x < 1427 then 1146 else 1808)) else (if x < 1430 then (if x < 1429 then 1253 else 1020) else (if x < 1431 then 812 else 1280))) else (if x < 1436 then (if x < 1434 then (if x < 1433 then 1996 else 582) else (if x < 1435 then 31 else 1219)) else (if x < 1438 then (if x < 1437 then 986 else 857) else (if x < 1439 then 1160 else 2037))))) else (if x < 1456 then (if x < 1448 then (if x < 1444 then (if x < 1442 then (if x < 1441 then 725 else 1604) else (if x < 1443 then 107 else 1636)) else (if x < 1446 then (if x < 1445 then 2039 else 966) else (if x < 1447 then 1787 else 1192))) else (if x < 1452 then (if x < 1450 then (if x < 1449 then 883 else 1732) else (if x < 1451 then 271 else 1242)) else (if x < 1454 then (if x < 1453 then 1972 else 25) else (if x < 1455 then 717 else 104)))) else (if x < 1464 then (if x < 1460 then (if x < 1458 then (if x < 1457 then 250 else 611) else (if x < 1459 then 1318 else 1387)) else (if x < 1462 then (if x < 1461 then 421 else 1541) else (if x < 1463 then 971 else 410))) else (if x < 1468 then (if x < 1466 then (if x < 1465 then 552 else 1168) else (if x < 1467 then 773 else 972)) else (if x < 1470 then (if x < 1469 then 1502 else 239) else (if x < 1471 then 1968 else 1558))))))

def conjugator_backward_1472 (x : ℕ) : ℕ :=
  (if x < 1504 then (if x < 1488 then (if x < 1480 then (if x < 1476 then (if x < 1474 then (if x < 1473 then 1939 else 1694) else (if x < 1475 then 1572 else 483)) else (if x < 1478 then (if x < 1477 then 206 else 566) else (if x < 1479 then 2036 else 196))) else (if x < 1484 then (if x < 1482 then (if x < 1481 then 1018 else 802) else (if x < 1483 then 1151 else 2047)) else (if x < 1486 then (if x < 1485 then 944 else 1247) else (if x < 1487 then 1937 else 478)))) else (if x < 1496 then (if x < 1492 then (if x < 1490 then (if x < 1489 then 1833 else 173) else (if x < 1491 then 705 else 2025)) else (if x < 1494 then (if x < 1493 then 891 else 499) else (if x < 1495 then 653 else 481))) else (if x < 1500 then (if x < 1498 then (if x < 1497 then 926 else 1533) else (if x < 1499 then 1878 else 1591)) else (if x < 1502 then (if x < 1501 then 698 else 1643) else (if x < 1503 then 1877 else 1691))))) else (if x < 1520 then (if x < 1512 then (if x < 1508 then (if x < 1506 then (if x < 1505 then 468 else 1465) else (if x < 1507 then 457 else 222)) else (if x < 1510 then (if x < 1509 then 1188 else 738) else (if x < 1511 then 1306 else 312))) else (if x < 1516 then (if x < 1514 then (if x < 1513 then 1491 else 820) else (if x < 1515 then 474 else 1453)) else (if x < 1518 then (if x < 1517 then 739 else 1535) else (if x < 1519 then 273 else 377)))) else (if x < 1528 then (if x < 1524 then (if x < 1522 then (if x < 1521 then 815 else 1898) else (if x < 1523 then 1261 else 1882)) else (if x < 1526 then (if x < 1525 then 1276 else 50) else (if x < 1527 then 1040 else 639))) else (if x < 1532 then (if x < 1530 then (if x < 1529 then 1650 else 1367) else (if x < 1531 then 1829 else 764)) else (if x < 1534 then (if x < 1533 then 408 else 1112) else (if x < 1535 then 848 else 341))))))

def conjugator_backward_1536 (x : ℕ) : ℕ :=
  (if x < 1568 then (if x < 1552 then (if x < 1544 then (if x < 1540 then (if x < 1538 then (if x < 1537 then 701 else 1086) else (if x < 1539 then 500 else 1936)) else (if x < 1542 then (if x < 1541 then 590 else 634) else (if x < 1543 then 712 else 875))) else (if x < 1548 then (if x < 1546 then (if x < 1545 then 1773 else 1672) else (if x < 1547 then 1109 else 147)) else (if x < 1550 then (if x < 1549 then 1562 else 1156) else (if x < 1551 then 502 else 1246)))) else (if x < 1560 then (if x < 1556 then (if x < 1554 then (if x < 1553 then 208 else 1340) else (if x < 1555 then 389 else 1926)) else (if x < 1558 then (if x < 1557 then 484 else 303) else (if x < 1559 then 1165 else 268))) else (if x < 1564 then (if x < 1562 then (if x < 1561 then 120 else 1284) else (if x < 1563 then 1081 else 1091)) else (if x < 1566 then (if x < 1565 then 1376 else 1422) else (if x < 1567 then 1626 else 1476))))) else (if x < 1584 then (if x < 1576 then (if x < 1572 then (if x < 1570 then (if x < 1569 then 1713 else 503) else (if x < 1571 then 320 else 1662)) else (if x < 1574 then (if x < 1573 then 1874 else 1561) else (if x < 1575 then 1301 else 1019))) else (if x < 1580 then (if x < 1578 then (if x < 1577 then 190 else 654) else (if x < 1579 then 1718 else 322)) else (if x < 1582 then (if x < 1581 then 1178 else 342) else (if x < 1583 then 1382 else 774)))) else (if x < 1592 then (if x < 1588 then (if x < 1586 then (if x < 1585 then 1970 else 549) else (if x < 1587 then 1973 else 259)) else (if x < 1590 then (if x < 1589 then 30 else 1964) else (if x < 1591 then 1116 else 17))) else (if x < 1596 then (if x < 1594 then (if x < 1593 then 2051 else 124) else (if x < 1595 then 470 else 8)) else (if x < 1598 then (if x < 1597 then 1976 else 1298) else (if x < 1599 then 723 else 680))))))

def conjugator_backward_1600 (x : ℕ) : ℕ :=
  (if x < 1632 then (if x < 1616 then (if x < 1608 then (if x < 1604 then (if x < 1602 then (if x < 1601 then 498 else 1475) else (if x < 1603 then 1036 else 795)) else (if x < 1606 then (if x < 1605 then 1032 else 1962) else (if x < 1607 then 172 else 435))) else (if x < 1612 then (if x < 1610 then (if x < 1609 then 1043 else 1777) else (if x < 1611 then 1734 else 1730)) else (if x < 1614 then (if x < 1613 then 167 else 1282) else (if x < 1615 then 668 else 561)))) else (if x < 1624 then (if x < 1620 then (if x < 1618 then (if x < 1617 then 1366 else 607) else (if x < 1619 then 840 else 1353)) else (if x < 1622 then (if x < 1621 then 906 else 1291) else (if x < 1623 then 783 else 1045))) else (if x < 1628 then (if x < 1626 then (if x < 1625 then 975 else 995) else (if x < 1627 then 852 else 509)) else (if x < 1630 then (if x < 1629 then 540 else 1748) else (if x < 1631 then 924 else 316))))) else (if x < 1648 then (if x < 1640 then (if x < 1636 then (if x < 1634 then (if x < 1633 then 1451 else 1351) else (if x < 1635 then 1009 else 681)) else (if x < 1638 then (if x < 1637 then 87 else 1184) else (if x < 1639 then 1063 else 1771))) else (if x < 1644 then (if x < 1642 then (if x < 1641 then 896 else 66) else (if x < 1643 then 729 else 267)) else (if x < 1646 then (if x < 1645 then 988 else 1194) else (if x < 1647 then 357 else 1580)))) else (if x < 1656 then (if x < 1652 then (if x < 1650 then (if x < 1649 then 1239 else 1342) else (if x < 1651 then 669 else 1635)) else (if x < 1654 then (if x < 1653 then 1585 else 713) else (if x < 1655 then 1606 else 536))) else (if x < 1660 then (if x < 1658 then (if x < 1657 then 1729 else 168) else (if x < 1659 then 514 else 1071)) else (if x < 1662 then (if x < 1661 then 1369 else 663) else (if x < 1663 then 293 else 1443))))))

def conjugator_backward_1664 (x : ℕ) : ℕ :=
  (if x < 1696 then (if x < 1680 then (if x < 1672 then (if x < 1668 then (if x < 1666 then (if x < 1665 then 1619 else 2055) else (if x < 1667 then 1790 else 1913)) else (if x < 1670 then (if x < 1669 then 1772 else 431) else (if x < 1671 then 176 else 385))) else (if x < 1676 then (if x < 1674 then (if x < 1673 then 1260 else 64) else (if x < 1675 then 1014 else 1292)) else (if x < 1678 then (if x < 1677 then 1406 else 1665) else (if x < 1679 then 724 else 171)))) else (if x < 1688 then (if x < 1684 then (if x < 1682 then (if x < 1681 then 1762 else 659) else (if x < 1683 then 904 else 928)) else (if x < 1686 then (if x < 1685 then 1903 else 749) else (if x < 1687 then 710 else 969))) else (if x < 1692 then (if x < 1690 then (if x < 1689 then 1432 else 932) else (if x < 1691 then 401 else 878)) else (if x < 1694 then (if x < 1693 then 1519 else 927) else (if x < 1695 then 1698 else 2042))))) else (if x < 1712 then (if x < 1704 then (if x < 1700 then (if x < 1698 then (if x < 1697 then 1908 else 302) else (if x < 1699 then 520 else 1567)) else (if x < 1702 then (if x < 1701 then 1804 else 1433) else (if x < 1703 then 567 else 650))) else (if x < 1708 then (if x < 1706 then (if x < 1705 then 1966 else 1263) else (if x < 1707 then 1557 else 1231)) else (if x < 1710 then (if x < 1709 then 550 else 1000) else (if x < 1711 then 1414 else 1513)))) else (if x < 1720 then (if x < 1716 then (if x < 1714 then (if x < 1713 then 123 else 1323) else (if x < 1715 then 91 else 469)) else (if x < 1718 then (if x < 1717 then 1819 else 1110) else (if x < 1719 then 244 else 1471))) else (if x < 1724 then (if x < 1722 then (if x < 1721 then 874 else 635) else (if x < 1723 then 832 else 647)) else (if x < 1726 then (if x < 1725 then 1133 else 1525) else (if x < 1727 then 55 else 776))))))

def conjugator_backward_1728 (x : ℕ) : ℕ :=
  (if x < 1760 then (if x < 1744 then (if x < 1736 then (if x < 1732 then (if x < 1730 then (if x < 1729 then 1807 else 70) else (if x < 1731 then 1226 else 596)) else (if x < 1734 then (if x < 1733 then 1481 else 1252) else (if x < 1735 then 1327 else 735))) else (if x < 1740 then (if x < 1738 then (if x < 1737 then 704 else 247) else (if x < 1739 then 1185 else 201)) else (if x < 1742 then (if x < 1741 then 782 else 1775) else (if x < 1743 then 839 else 1880)))) else (if x < 1752 then (if x < 1748 then (if x < 1746 then (if x < 1745 then 1766 else 384) else (if x < 1747 then 489 else 1914)) else (if x < 1750 then (if x < 1749 then 1182 else 246) else (if x < 1751 then 1705 else 1200))) else (if x < 1756 then (if x < 1754 then (if x < 1753 then 46 else 221) else (if x < 1755 then 1751 else 1667)) else (if x < 1758 then (if x < 1757 then 219 else 834) else (if x < 1759 then 1978 else 1990))))) else (if x < 1776 then (if x < 1768 then (if x < 1764 then (if x < 1762 then (if x < 1761 then 1866 else 306) else (if x < 1763 then 1942 else 1707)) else (if x < 1766 then (if x < 1765 then 1859 else 2012) else (if x < 1767 then 1627 else 1590))) else (if x < 1772 then (if x < 1770 then (if x < 1769 then 1056 else 1825) else (if x < 1771 then 786 else 922)) else (if x < 1774 then (if x < 1773 then 1612 else 1117) else (if x < 1775 then 1555 else 1483)))) else (if x < 1784 then (if x < 1780 then (if x < 1778 then (if x < 1777 then 209 else 487) else (if x < 1779 then 1028 else 805)) else (if x < 1782 then (if x < 1781 then 1173 else 2020) else (if x < 1783 then 1554 else 1039))) else (if x < 1788 then (if x < 1786 then (if x < 1785 then 192 else 490) else (if x < 1787 then 154 else 1921)) else (if x < 1790 then (if x < 1789 then 614 else 1527) else (if x < 1791 then 462 else 1008))))))

def conjugator_backward_1792 (x : ℕ) : ℕ :=
  (if x < 1824 then (if x < 1808 then (if x < 1800 then (if x < 1796 then (if x < 1794 then (if x < 1793 then 1849 else 592) else (if x < 1795 then 1167 else 570)) else (if x < 1798 then (if x < 1797 then 1026 else 359) else (if x < 1799 then 957 else 1210))) else (if x < 1804 then (if x < 1802 then (if x < 1801 then 727 else 6) else (if x < 1803 then 1062 else 187)) else (if x < 1806 then (if x < 1805 then 1742 else 903) else (if x < 1807 then 1426 else 447)))) else (if x < 1816 then (if x < 1812 then (if x < 1810 then (if x < 1809 then 1912 else 1401) else (if x < 1811 then 1981 else 973)) else (if x < 1814 then (if x < 1813 then 1669 else 1905) else (if x < 1815 then 248 else 1587))) else (if x < 1820 then (if x < 1818 then (if x < 1817 then 1737 else 792) else (if x < 1819 then 1362 else 1938)) else (if x < 1822 then (if x < 1821 then 689 else 270) else (if x < 1823 then 1420 else 728))))) else (if x < 1840 then (if x < 1832 then (if x < 1828 then (if x < 1826 then (if x < 1825 then 1054 else 1873) else (if x < 1827 then 827 else 1958)) else (if x < 1830 then (if x < 1829 then 179 else 1373) else (if x < 1831 then 231 else 844))) else (if x < 1836 then (if x < 1834 then (if x < 1833 then 1041 else 894) else (if x < 1835 then 613 else 952)) else (if x < 1838 then (if x < 1837 then 1113 else 1867) else (if x < 1839 then 1786 else 289)))) else (if x < 1848 then (if x < 1844 then (if x < 1842 then (if x < 1841 then 1101 else 1270) else (if x < 1843 then 1935 else 5)) else (if x < 1846 then (if x < 1845 then 622 else 1437) else (if x < 1847 then 67 else 1865))) else (if x < 1852 then (if x < 1850 then (if x < 1849 then 1057 else 1649) else (if x < 1851 then 763 else 876)) else (if x < 1854 then (if x < 1853 then 298 else 1965) else (if x < 1855 then 2040 else 347))))))

def conjugator_backward_1856 (x : ℕ) : ℕ :=
  (if x < 1888 then (if x < 1872 then (if x < 1864 then (if x < 1860 then (if x < 1858 then (if x < 1857 then 950 else 68) else (if x < 1859 then 1319 else 1697)) else (if x < 1862 then (if x < 1861 then 523 else 338) else (if x < 1863 then 249 else 916))) else (if x < 1868 then (if x < 1866 then (if x < 1865 then 1447 else 184) else (if x < 1867 then 1441 else 48)) else (if x < 1870 then (if x < 1869 then 970 else 1196) else (if x < 1871 then 925 else 1548)))) else (if x < 1880 then (if x < 1876 then (if x < 1874 then (if x < 1873 then 909 else 1212) else (if x < 1875 then 2002 else 54)) else (if x < 1878 then (if x < 1877 then 1379 else 188) else (if x < 1879 then 1161 else 288))) else (if x < 1884 then (if x < 1882 then (if x < 1881 then 1839 else 1823) else (if x < 1883 then 1204 else 1655)) else (if x < 1886 then (if x < 1885 then 1228 else 1203) else (if x < 1887 then 286 else 1715))))) else (if x < 1904 then (if x < 1896 then (if x < 1892 then (if x < 1890 then (if x < 1889 then 1577 else 632) else (if x < 1891 then 292 else 1750)) else (if x < 1894 then (if x < 1893 then 235 else 143) else (if x < 1895 then 1605 else 1719))) else (if x < 1900 then (if x < 1898 then (if x < 1897 then 1830 else 438) else (if x < 1899 then 1520 else 1176)) else (if x < 1902 then (if x < 1901 then 1637 else 1108) else (if x < 1903 then 532 else 833)))) else (if x < 1912 then (if x < 1908 then (if x < 1906 then (if x < 1905 then 1679 else 1692) else (if x < 1907 then 993 else 1083)) else (if x < 1910 then (if x < 1909 then 826 else 52) else (if x < 1911 then 1286 else 1918))) else (if x < 1916 then (if x < 1914 then (if x < 1913 then 1956 else 228) else (if x < 1915 then 1896 else 363)) else (if x < 1918 then (if x < 1917 then 217 else 460) else (if x < 1919 then 482 else 696))))))

def conjugator_backward_1920 (x : ℕ) : ℕ :=
  (if x < 1952 then (if x < 1936 then (if x < 1928 then (if x < 1924 then (if x < 1922 then (if x < 1921 then 946 else 587) else (if x < 1923 then 651 else 1468)) else (if x < 1926 then (if x < 1925 then 638 else 1048) else (if x < 1927 then 1827 else 234))) else (if x < 1932 then (if x < 1930 then (if x < 1929 then 616 else 1324) else (if x < 1931 then 1987 else 310)) else (if x < 1934 then (if x < 1933 then 1885 else 980) else (if x < 1935 then 1815 else 730)))) else (if x < 1944 then (if x < 1940 then (if x < 1938 then (if x < 1937 then 1895 else 1264) else (if x < 1939 then 1552 else 633)) else (if x < 1942 then (if x < 1941 then 700 else 1170) else (if x < 1943 then 1997 else 1139))) else (if x < 1948 then (if x < 1946 then (if x < 1945 then 106 else 538) else (if x < 1947 then 1333 else 1547)) else (if x < 1950 then (if x < 1949 then 691 else 545) else (if x < 1951 then 1640 else 1275))))) else (if x < 1968 then (if x < 1960 then (if x < 1956 then (if x < 1954 then (if x < 1953 then 811 else 1294) else (if x < 1955 then 910 else 486)) else (if x < 1958 then (if x < 1957 then 858 else 985) else (if x < 1959 then 354 else 899))) else (if x < 1964 then (if x < 1962 then (if x < 1961 then 1850 else 1563) else (if x < 1963 then 914 else 1852)) else (if x < 1966 then (if x < 1965 then 1221 else 1419) else (if x < 1967 then 1668 else 1458)))) else (if x < 1976 then (if x < 1972 then (if x < 1970 then (if x < 1969 then 434 else 793) else (if x < 1971 then 806 else 441)) else (if x < 1974 then (if x < 1973 then 1449 else 1114) else (if x < 1975 then 1518 else 1189))) else (if x < 1980 then (if x < 1978 then (if x < 1977 then 93 else 455) else (if x < 1979 then 311 else 1302)) else (if x < 1982 then (if x < 1981 then 594 else 1897) else (if x < 1983 then 694 else 99))))))

def conjugator_backward_1984 (x : ℕ) : ℕ :=
  (if x < 2016 then (if x < 2000 then (if x < 1992 then (if x < 1988 then (if x < 1986 then (if x < 1985 then 1892 else 661) else (if x < 1987 then 1365 else 301)) else (if x < 1990 then (if x < 1989 then 229 else 1159) else (if x < 1991 then 452 else 1683))) else (if x < 1996 then (if x < 1994 then (if x < 1993 then 409 else 1416) else (if x < 1995 then 1440 else 849)) else (if x < 1998 then (if x < 1997 then 1070 else 1755) else (if x < 1999 then 1955 else 1166)))) else (if x < 2008 then (if x < 2004 then (if x < 2002 then (if x < 2001 then 1027 else 493) else (if x < 2003 then 1124 else 336)) else (if x < 2006 then (if x < 2005 then 1230 else 1257) else (if x < 2007 then 1396 else 1123))) else (if x < 2012 then (if x < 2010 then (if x < 2009 then 28 else 1917) else (if x < 2011 then 2015 else 1138)) else (if x < 2014 then (if x < 2013 then 1067 else 900) else (if x < 2015 then 308 else 583))))) else (if x < 2032 then (if x < 2024 then (if x < 2020 then (if x < 2018 then (if x < 2017 then 1995 else 1716) else (if x < 2019 then 442 else 526)) else (if x < 2022 then (if x < 2021 then 1259 else 1768) else (if x < 2023 then 742 else 1735))) else (if x < 2028 then (if x < 2026 then (if x < 2025 then 1377 else 671) else (if x < 2027 then 1313 else 1601)) else (if x < 2030 then (if x < 2029 then 1135 else 2008) else (if x < 2031 then 1759 else 1961)))) else (if x < 2040 then (if x < 2036 then (if x < 2034 then (if x < 2033 then 784 else 1824) else (if x < 2035 then 116 else 1629)) else (if x < 2038 then (if x < 2037 then 1354 else 1092) else (if x < 2039 then 1861 else 676))) else (if x < 2044 then (if x < 2042 then (if x < 2041 then 2004 else 1514) else (if x < 2043 then 1983 else 1602)) else (if x < 2046 then (if x < 2045 then 1791 else 574) else (if x < 2047 then 1794 else 174))))))

def conjugator_backward_2048 (x : ℕ) : ℕ :=
  (if x < 2053 then (if x < 2050 then (if x < 2049 then 1501 else 847) else (if x < 2051 then 1163 else (if x < 2052 then 1556 else 785))) else (if x < 2055 then (if x < 2054 then 2001 else 1571) else (if x < 2056 then 296 else (if x < 2057 then 24 else 433))))

def conjugator_backward (v : Fin 2058) : Fin 2058 :=
  let x := v.val
  ⟨((if x < 1024 then (if x < 512 then (if x < 256 then (if x < 128 then (if x < 64 then conjugator_backward_0 x else conjugator_backward_64 x) else (if x < 192 then conjugator_backward_128 x else conjugator_backward_192 x)) else (if x < 384 then (if x < 320 then conjugator_backward_256 x else conjugator_backward_320 x) else (if x < 448 then conjugator_backward_384 x else conjugator_backward_448 x))) else (if x < 768 then (if x < 640 then (if x < 576 then conjugator_backward_512 x else conjugator_backward_576 x) else (if x < 704 then conjugator_backward_640 x else conjugator_backward_704 x)) else (if x < 896 then (if x < 832 then conjugator_backward_768 x else conjugator_backward_832 x) else (if x < 960 then conjugator_backward_896 x else conjugator_backward_960 x)))) else (if x < 1536 then (if x < 1280 then (if x < 1152 then (if x < 1088 then conjugator_backward_1024 x else conjugator_backward_1088 x) else (if x < 1216 then conjugator_backward_1152 x else conjugator_backward_1216 x)) else (if x < 1408 then (if x < 1344 then conjugator_backward_1280 x else conjugator_backward_1344 x) else (if x < 1472 then conjugator_backward_1408 x else conjugator_backward_1472 x))) else (if x < 1792 then (if x < 1664 then (if x < 1600 then conjugator_backward_1536 x else conjugator_backward_1600 x) else (if x < 1728 then conjugator_backward_1664 x else conjugator_backward_1728 x)) else (if x < 1920 then (if x < 1856 then conjugator_backward_1792 x else conjugator_backward_1856 x) else (if x < 1984 then conjugator_backward_1920 x else (if x < 2048 then conjugator_backward_1984 x else conjugator_backward_2048 x))))))) % 2058, Nat.mod_lt _ (by decide)⟩

abbrev conjugator_leftInvPredicate (x : Fin 2058) : Prop := conjugator_backward (conjugator_forward x) = x

private theorem conjugator_leftInv_block0 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block1 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block2 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block3 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block4 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block5 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block6 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block7 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block8 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block9 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block10 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block11 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block12 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block13 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block14 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block15 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block16 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block17 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block18 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block19 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block20 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block21 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block22 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block23 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block24 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block25 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block26 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block27 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block28 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block29 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block30 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block31 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem conjugator_leftInv_block32 : checkFin 64 (fun j => decide (conjugator_leftInvPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem conjugator_leftInv : ∀ x, conjugator_leftInvPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ conjugator_leftInv_block0
  · exact allFin _ _ conjugator_leftInv_block1
  · exact allFin _ _ conjugator_leftInv_block2
  · exact allFin _ _ conjugator_leftInv_block3
  · exact allFin _ _ conjugator_leftInv_block4
  · exact allFin _ _ conjugator_leftInv_block5
  · exact allFin _ _ conjugator_leftInv_block6
  · exact allFin _ _ conjugator_leftInv_block7
  · exact allFin _ _ conjugator_leftInv_block8
  · exact allFin _ _ conjugator_leftInv_block9
  · exact allFin _ _ conjugator_leftInv_block10
  · exact allFin _ _ conjugator_leftInv_block11
  · exact allFin _ _ conjugator_leftInv_block12
  · exact allFin _ _ conjugator_leftInv_block13
  · exact allFin _ _ conjugator_leftInv_block14
  · exact allFin _ _ conjugator_leftInv_block15
  · exact allFin _ _ conjugator_leftInv_block16
  · exact allFin _ _ conjugator_leftInv_block17
  · exact allFin _ _ conjugator_leftInv_block18
  · exact allFin _ _ conjugator_leftInv_block19
  · exact allFin _ _ conjugator_leftInv_block20
  · exact allFin _ _ conjugator_leftInv_block21
  · exact allFin _ _ conjugator_leftInv_block22
  · exact allFin _ _ conjugator_leftInv_block23
  · exact allFin _ _ conjugator_leftInv_block24
  · exact allFin _ _ conjugator_leftInv_block25
  · exact allFin _ _ conjugator_leftInv_block26
  · exact allFin _ _ conjugator_leftInv_block27
  · exact allFin _ _ conjugator_leftInv_block28
  · exact allFin _ _ conjugator_leftInv_block29
  · exact allFin _ _ conjugator_leftInv_block30
  · exact allFin _ _ conjugator_leftInv_block31
  · exact allFin _ _ conjugator_leftInv_block32

abbrev conjugator_rightInvPredicate (x : Fin 2058) : Prop := conjugator_forward (conjugator_backward x) = x

private theorem conjugator_rightInv_block0 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block1 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block2 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block3 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block4 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block5 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block6 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block7 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block8 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block9 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block10 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block11 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block12 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block13 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block14 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block15 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block16 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block17 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block18 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block19 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block20 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block21 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block22 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block23 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block24 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block25 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block26 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block27 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block28 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block29 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block30 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block31 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem conjugator_rightInv_block32 : checkFin 64 (fun j => decide (conjugator_rightInvPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem conjugator_rightInv : ∀ x, conjugator_rightInvPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ conjugator_rightInv_block0
  · exact allFin _ _ conjugator_rightInv_block1
  · exact allFin _ _ conjugator_rightInv_block2
  · exact allFin _ _ conjugator_rightInv_block3
  · exact allFin _ _ conjugator_rightInv_block4
  · exact allFin _ _ conjugator_rightInv_block5
  · exact allFin _ _ conjugator_rightInv_block6
  · exact allFin _ _ conjugator_rightInv_block7
  · exact allFin _ _ conjugator_rightInv_block8
  · exact allFin _ _ conjugator_rightInv_block9
  · exact allFin _ _ conjugator_rightInv_block10
  · exact allFin _ _ conjugator_rightInv_block11
  · exact allFin _ _ conjugator_rightInv_block12
  · exact allFin _ _ conjugator_rightInv_block13
  · exact allFin _ _ conjugator_rightInv_block14
  · exact allFin _ _ conjugator_rightInv_block15
  · exact allFin _ _ conjugator_rightInv_block16
  · exact allFin _ _ conjugator_rightInv_block17
  · exact allFin _ _ conjugator_rightInv_block18
  · exact allFin _ _ conjugator_rightInv_block19
  · exact allFin _ _ conjugator_rightInv_block20
  · exact allFin _ _ conjugator_rightInv_block21
  · exact allFin _ _ conjugator_rightInv_block22
  · exact allFin _ _ conjugator_rightInv_block23
  · exact allFin _ _ conjugator_rightInv_block24
  · exact allFin _ _ conjugator_rightInv_block25
  · exact allFin _ _ conjugator_rightInv_block26
  · exact allFin _ _ conjugator_rightInv_block27
  · exact allFin _ _ conjugator_rightInv_block28
  · exact allFin _ _ conjugator_rightInv_block29
  · exact allFin _ _ conjugator_rightInv_block30
  · exact allFin _ _ conjugator_rightInv_block31
  · exact allFin _ _ conjugator_rightInv_block32

def conjugator : Equiv.Perm (Fin 2058) where
  toFun := conjugator_forward
  invFun := conjugator_backward
  left_inv := conjugator_leftInv
  right_inv := conjugator_rightInv

def forwardWord : Fin 4 → List (Fin 4 × ℤ)
  | 0 => [(0, 1), (3, 1), (1, 1), (0, 1), (3, 1), (0, 1)]
  | 1 => [(1, 1), (3, 1), (0, 1), (3, 1), (1, 1)]
  | 2 => [(3, 1), (2, 1), (3, 1), (2, 1), (1, 1), (0, 1), (3, 1), (1, 1), (0, 1)]
  | 3 => [(0, 1), (3, 1), (1, 1), (2, 1), (3, 1), (1, 1), (0, 1)]

def backwardWord : Fin 4 → List (Fin 4 × ℤ)
  | 0 => [(3, 1), (0, 1), (2, 1), (3, 1), (1, 1), (3, 1), (2, 1), (3, 1), (0, 1)]
  | 1 => [(3, 1), (2, 1), (3, 1), (1, 1), (3, 1), (0, 1), (2, 1), (3, 1)]
  | 2 => [(3, 1), (1, 1), (3, 1), (0, 1), (2, 1), (3, 1), (2, 1), (1, 1), (0, 1)]
  | 3 => [(3, 1), (2, 1), (3, 1), (2, 1), (0, 1), (2, 1), (0, 1)]

def sourceGenerator (k : Fin 4) := Pair00.generatorTable ⟨k.val + 2, by omega⟩
def targetGenerator (k : Fin 4) := Pair10.generatorTable ⟨k.val + 2, by omega⟩

abbrev forward_0_actionPredicate (x : Fin 2058) : Prop := (conjugator⁻¹ * sourceGenerator 0 * conjugator) x = (evalSigned targetGenerator (forwardWord 0)) x

private theorem forward_0_action_block0 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem forward_0_action_block1 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem forward_0_action_block2 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem forward_0_action_block3 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem forward_0_action_block4 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem forward_0_action_block5 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem forward_0_action_block6 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem forward_0_action_block7 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem forward_0_action_block8 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem forward_0_action_block9 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem forward_0_action_block10 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem forward_0_action_block11 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem forward_0_action_block12 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem forward_0_action_block13 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem forward_0_action_block14 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem forward_0_action_block15 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem forward_0_action_block16 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem forward_0_action_block17 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem forward_0_action_block18 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem forward_0_action_block19 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem forward_0_action_block20 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem forward_0_action_block21 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem forward_0_action_block22 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem forward_0_action_block23 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem forward_0_action_block24 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem forward_0_action_block25 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem forward_0_action_block26 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem forward_0_action_block27 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem forward_0_action_block28 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem forward_0_action_block29 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem forward_0_action_block30 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem forward_0_action_block31 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem forward_0_action_block32 : checkFin 64 (fun j => decide (forward_0_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem forward_0_action : ∀ x, forward_0_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ forward_0_action_block0
  · exact allFin _ _ forward_0_action_block1
  · exact allFin _ _ forward_0_action_block2
  · exact allFin _ _ forward_0_action_block3
  · exact allFin _ _ forward_0_action_block4
  · exact allFin _ _ forward_0_action_block5
  · exact allFin _ _ forward_0_action_block6
  · exact allFin _ _ forward_0_action_block7
  · exact allFin _ _ forward_0_action_block8
  · exact allFin _ _ forward_0_action_block9
  · exact allFin _ _ forward_0_action_block10
  · exact allFin _ _ forward_0_action_block11
  · exact allFin _ _ forward_0_action_block12
  · exact allFin _ _ forward_0_action_block13
  · exact allFin _ _ forward_0_action_block14
  · exact allFin _ _ forward_0_action_block15
  · exact allFin _ _ forward_0_action_block16
  · exact allFin _ _ forward_0_action_block17
  · exact allFin _ _ forward_0_action_block18
  · exact allFin _ _ forward_0_action_block19
  · exact allFin _ _ forward_0_action_block20
  · exact allFin _ _ forward_0_action_block21
  · exact allFin _ _ forward_0_action_block22
  · exact allFin _ _ forward_0_action_block23
  · exact allFin _ _ forward_0_action_block24
  · exact allFin _ _ forward_0_action_block25
  · exact allFin _ _ forward_0_action_block26
  · exact allFin _ _ forward_0_action_block27
  · exact allFin _ _ forward_0_action_block28
  · exact allFin _ _ forward_0_action_block29
  · exact allFin _ _ forward_0_action_block30
  · exact allFin _ _ forward_0_action_block31
  · exact allFin _ _ forward_0_action_block32

theorem forward_0 : conjugator⁻¹ * sourceGenerator 0 * conjugator = evalSigned targetGenerator (forwardWord 0) := Equiv.ext forward_0_action

abbrev backward_0_actionPredicate (x : Fin 2058) : Prop := (conjugator * targetGenerator 0 * conjugator⁻¹) x = (evalSigned sourceGenerator (backwardWord 0)) x

private theorem backward_0_action_block0 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem backward_0_action_block1 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem backward_0_action_block2 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem backward_0_action_block3 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem backward_0_action_block4 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem backward_0_action_block5 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem backward_0_action_block6 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem backward_0_action_block7 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem backward_0_action_block8 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem backward_0_action_block9 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem backward_0_action_block10 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem backward_0_action_block11 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem backward_0_action_block12 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem backward_0_action_block13 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem backward_0_action_block14 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem backward_0_action_block15 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem backward_0_action_block16 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem backward_0_action_block17 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem backward_0_action_block18 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem backward_0_action_block19 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem backward_0_action_block20 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem backward_0_action_block21 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem backward_0_action_block22 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem backward_0_action_block23 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem backward_0_action_block24 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem backward_0_action_block25 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem backward_0_action_block26 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem backward_0_action_block27 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem backward_0_action_block28 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem backward_0_action_block29 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem backward_0_action_block30 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem backward_0_action_block31 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem backward_0_action_block32 : checkFin 64 (fun j => decide (backward_0_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem backward_0_action : ∀ x, backward_0_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ backward_0_action_block0
  · exact allFin _ _ backward_0_action_block1
  · exact allFin _ _ backward_0_action_block2
  · exact allFin _ _ backward_0_action_block3
  · exact allFin _ _ backward_0_action_block4
  · exact allFin _ _ backward_0_action_block5
  · exact allFin _ _ backward_0_action_block6
  · exact allFin _ _ backward_0_action_block7
  · exact allFin _ _ backward_0_action_block8
  · exact allFin _ _ backward_0_action_block9
  · exact allFin _ _ backward_0_action_block10
  · exact allFin _ _ backward_0_action_block11
  · exact allFin _ _ backward_0_action_block12
  · exact allFin _ _ backward_0_action_block13
  · exact allFin _ _ backward_0_action_block14
  · exact allFin _ _ backward_0_action_block15
  · exact allFin _ _ backward_0_action_block16
  · exact allFin _ _ backward_0_action_block17
  · exact allFin _ _ backward_0_action_block18
  · exact allFin _ _ backward_0_action_block19
  · exact allFin _ _ backward_0_action_block20
  · exact allFin _ _ backward_0_action_block21
  · exact allFin _ _ backward_0_action_block22
  · exact allFin _ _ backward_0_action_block23
  · exact allFin _ _ backward_0_action_block24
  · exact allFin _ _ backward_0_action_block25
  · exact allFin _ _ backward_0_action_block26
  · exact allFin _ _ backward_0_action_block27
  · exact allFin _ _ backward_0_action_block28
  · exact allFin _ _ backward_0_action_block29
  · exact allFin _ _ backward_0_action_block30
  · exact allFin _ _ backward_0_action_block31
  · exact allFin _ _ backward_0_action_block32

theorem backward_0 : conjugator * targetGenerator 0 * conjugator⁻¹ = evalSigned sourceGenerator (backwardWord 0) := Equiv.ext backward_0_action

abbrev forward_1_actionPredicate (x : Fin 2058) : Prop := (conjugator⁻¹ * sourceGenerator 1 * conjugator) x = (evalSigned targetGenerator (forwardWord 1)) x

private theorem forward_1_action_block0 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem forward_1_action_block1 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem forward_1_action_block2 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem forward_1_action_block3 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem forward_1_action_block4 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem forward_1_action_block5 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem forward_1_action_block6 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem forward_1_action_block7 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem forward_1_action_block8 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem forward_1_action_block9 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem forward_1_action_block10 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem forward_1_action_block11 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem forward_1_action_block12 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem forward_1_action_block13 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem forward_1_action_block14 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem forward_1_action_block15 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem forward_1_action_block16 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem forward_1_action_block17 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem forward_1_action_block18 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem forward_1_action_block19 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem forward_1_action_block20 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem forward_1_action_block21 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem forward_1_action_block22 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem forward_1_action_block23 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem forward_1_action_block24 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem forward_1_action_block25 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem forward_1_action_block26 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem forward_1_action_block27 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem forward_1_action_block28 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem forward_1_action_block29 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem forward_1_action_block30 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem forward_1_action_block31 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem forward_1_action_block32 : checkFin 64 (fun j => decide (forward_1_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem forward_1_action : ∀ x, forward_1_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ forward_1_action_block0
  · exact allFin _ _ forward_1_action_block1
  · exact allFin _ _ forward_1_action_block2
  · exact allFin _ _ forward_1_action_block3
  · exact allFin _ _ forward_1_action_block4
  · exact allFin _ _ forward_1_action_block5
  · exact allFin _ _ forward_1_action_block6
  · exact allFin _ _ forward_1_action_block7
  · exact allFin _ _ forward_1_action_block8
  · exact allFin _ _ forward_1_action_block9
  · exact allFin _ _ forward_1_action_block10
  · exact allFin _ _ forward_1_action_block11
  · exact allFin _ _ forward_1_action_block12
  · exact allFin _ _ forward_1_action_block13
  · exact allFin _ _ forward_1_action_block14
  · exact allFin _ _ forward_1_action_block15
  · exact allFin _ _ forward_1_action_block16
  · exact allFin _ _ forward_1_action_block17
  · exact allFin _ _ forward_1_action_block18
  · exact allFin _ _ forward_1_action_block19
  · exact allFin _ _ forward_1_action_block20
  · exact allFin _ _ forward_1_action_block21
  · exact allFin _ _ forward_1_action_block22
  · exact allFin _ _ forward_1_action_block23
  · exact allFin _ _ forward_1_action_block24
  · exact allFin _ _ forward_1_action_block25
  · exact allFin _ _ forward_1_action_block26
  · exact allFin _ _ forward_1_action_block27
  · exact allFin _ _ forward_1_action_block28
  · exact allFin _ _ forward_1_action_block29
  · exact allFin _ _ forward_1_action_block30
  · exact allFin _ _ forward_1_action_block31
  · exact allFin _ _ forward_1_action_block32

theorem forward_1 : conjugator⁻¹ * sourceGenerator 1 * conjugator = evalSigned targetGenerator (forwardWord 1) := Equiv.ext forward_1_action

abbrev backward_1_actionPredicate (x : Fin 2058) : Prop := (conjugator * targetGenerator 1 * conjugator⁻¹) x = (evalSigned sourceGenerator (backwardWord 1)) x

private theorem backward_1_action_block0 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem backward_1_action_block1 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem backward_1_action_block2 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem backward_1_action_block3 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem backward_1_action_block4 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem backward_1_action_block5 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem backward_1_action_block6 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem backward_1_action_block7 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem backward_1_action_block8 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem backward_1_action_block9 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem backward_1_action_block10 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem backward_1_action_block11 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem backward_1_action_block12 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem backward_1_action_block13 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem backward_1_action_block14 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem backward_1_action_block15 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem backward_1_action_block16 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem backward_1_action_block17 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem backward_1_action_block18 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem backward_1_action_block19 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem backward_1_action_block20 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem backward_1_action_block21 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem backward_1_action_block22 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem backward_1_action_block23 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem backward_1_action_block24 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem backward_1_action_block25 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem backward_1_action_block26 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem backward_1_action_block27 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem backward_1_action_block28 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem backward_1_action_block29 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem backward_1_action_block30 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem backward_1_action_block31 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem backward_1_action_block32 : checkFin 64 (fun j => decide (backward_1_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem backward_1_action : ∀ x, backward_1_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ backward_1_action_block0
  · exact allFin _ _ backward_1_action_block1
  · exact allFin _ _ backward_1_action_block2
  · exact allFin _ _ backward_1_action_block3
  · exact allFin _ _ backward_1_action_block4
  · exact allFin _ _ backward_1_action_block5
  · exact allFin _ _ backward_1_action_block6
  · exact allFin _ _ backward_1_action_block7
  · exact allFin _ _ backward_1_action_block8
  · exact allFin _ _ backward_1_action_block9
  · exact allFin _ _ backward_1_action_block10
  · exact allFin _ _ backward_1_action_block11
  · exact allFin _ _ backward_1_action_block12
  · exact allFin _ _ backward_1_action_block13
  · exact allFin _ _ backward_1_action_block14
  · exact allFin _ _ backward_1_action_block15
  · exact allFin _ _ backward_1_action_block16
  · exact allFin _ _ backward_1_action_block17
  · exact allFin _ _ backward_1_action_block18
  · exact allFin _ _ backward_1_action_block19
  · exact allFin _ _ backward_1_action_block20
  · exact allFin _ _ backward_1_action_block21
  · exact allFin _ _ backward_1_action_block22
  · exact allFin _ _ backward_1_action_block23
  · exact allFin _ _ backward_1_action_block24
  · exact allFin _ _ backward_1_action_block25
  · exact allFin _ _ backward_1_action_block26
  · exact allFin _ _ backward_1_action_block27
  · exact allFin _ _ backward_1_action_block28
  · exact allFin _ _ backward_1_action_block29
  · exact allFin _ _ backward_1_action_block30
  · exact allFin _ _ backward_1_action_block31
  · exact allFin _ _ backward_1_action_block32

theorem backward_1 : conjugator * targetGenerator 1 * conjugator⁻¹ = evalSigned sourceGenerator (backwardWord 1) := Equiv.ext backward_1_action

abbrev forward_2_actionPredicate (x : Fin 2058) : Prop := (conjugator⁻¹ * sourceGenerator 2 * conjugator) x = (evalSigned targetGenerator (forwardWord 2)) x

private theorem forward_2_action_block0 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem forward_2_action_block1 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem forward_2_action_block2 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem forward_2_action_block3 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem forward_2_action_block4 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem forward_2_action_block5 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem forward_2_action_block6 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem forward_2_action_block7 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem forward_2_action_block8 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem forward_2_action_block9 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem forward_2_action_block10 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem forward_2_action_block11 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem forward_2_action_block12 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem forward_2_action_block13 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem forward_2_action_block14 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem forward_2_action_block15 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem forward_2_action_block16 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem forward_2_action_block17 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem forward_2_action_block18 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem forward_2_action_block19 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem forward_2_action_block20 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem forward_2_action_block21 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem forward_2_action_block22 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem forward_2_action_block23 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem forward_2_action_block24 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem forward_2_action_block25 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem forward_2_action_block26 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem forward_2_action_block27 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem forward_2_action_block28 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem forward_2_action_block29 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem forward_2_action_block30 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem forward_2_action_block31 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem forward_2_action_block32 : checkFin 64 (fun j => decide (forward_2_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem forward_2_action : ∀ x, forward_2_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ forward_2_action_block0
  · exact allFin _ _ forward_2_action_block1
  · exact allFin _ _ forward_2_action_block2
  · exact allFin _ _ forward_2_action_block3
  · exact allFin _ _ forward_2_action_block4
  · exact allFin _ _ forward_2_action_block5
  · exact allFin _ _ forward_2_action_block6
  · exact allFin _ _ forward_2_action_block7
  · exact allFin _ _ forward_2_action_block8
  · exact allFin _ _ forward_2_action_block9
  · exact allFin _ _ forward_2_action_block10
  · exact allFin _ _ forward_2_action_block11
  · exact allFin _ _ forward_2_action_block12
  · exact allFin _ _ forward_2_action_block13
  · exact allFin _ _ forward_2_action_block14
  · exact allFin _ _ forward_2_action_block15
  · exact allFin _ _ forward_2_action_block16
  · exact allFin _ _ forward_2_action_block17
  · exact allFin _ _ forward_2_action_block18
  · exact allFin _ _ forward_2_action_block19
  · exact allFin _ _ forward_2_action_block20
  · exact allFin _ _ forward_2_action_block21
  · exact allFin _ _ forward_2_action_block22
  · exact allFin _ _ forward_2_action_block23
  · exact allFin _ _ forward_2_action_block24
  · exact allFin _ _ forward_2_action_block25
  · exact allFin _ _ forward_2_action_block26
  · exact allFin _ _ forward_2_action_block27
  · exact allFin _ _ forward_2_action_block28
  · exact allFin _ _ forward_2_action_block29
  · exact allFin _ _ forward_2_action_block30
  · exact allFin _ _ forward_2_action_block31
  · exact allFin _ _ forward_2_action_block32

theorem forward_2 : conjugator⁻¹ * sourceGenerator 2 * conjugator = evalSigned targetGenerator (forwardWord 2) := Equiv.ext forward_2_action

abbrev backward_2_actionPredicate (x : Fin 2058) : Prop := (conjugator * targetGenerator 2 * conjugator⁻¹) x = (evalSigned sourceGenerator (backwardWord 2)) x

private theorem backward_2_action_block0 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem backward_2_action_block1 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem backward_2_action_block2 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem backward_2_action_block3 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem backward_2_action_block4 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem backward_2_action_block5 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem backward_2_action_block6 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem backward_2_action_block7 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem backward_2_action_block8 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem backward_2_action_block9 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem backward_2_action_block10 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem backward_2_action_block11 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem backward_2_action_block12 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem backward_2_action_block13 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem backward_2_action_block14 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem backward_2_action_block15 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem backward_2_action_block16 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem backward_2_action_block17 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem backward_2_action_block18 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem backward_2_action_block19 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem backward_2_action_block20 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem backward_2_action_block21 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem backward_2_action_block22 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem backward_2_action_block23 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem backward_2_action_block24 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem backward_2_action_block25 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem backward_2_action_block26 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem backward_2_action_block27 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem backward_2_action_block28 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem backward_2_action_block29 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem backward_2_action_block30 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem backward_2_action_block31 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem backward_2_action_block32 : checkFin 64 (fun j => decide (backward_2_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem backward_2_action : ∀ x, backward_2_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ backward_2_action_block0
  · exact allFin _ _ backward_2_action_block1
  · exact allFin _ _ backward_2_action_block2
  · exact allFin _ _ backward_2_action_block3
  · exact allFin _ _ backward_2_action_block4
  · exact allFin _ _ backward_2_action_block5
  · exact allFin _ _ backward_2_action_block6
  · exact allFin _ _ backward_2_action_block7
  · exact allFin _ _ backward_2_action_block8
  · exact allFin _ _ backward_2_action_block9
  · exact allFin _ _ backward_2_action_block10
  · exact allFin _ _ backward_2_action_block11
  · exact allFin _ _ backward_2_action_block12
  · exact allFin _ _ backward_2_action_block13
  · exact allFin _ _ backward_2_action_block14
  · exact allFin _ _ backward_2_action_block15
  · exact allFin _ _ backward_2_action_block16
  · exact allFin _ _ backward_2_action_block17
  · exact allFin _ _ backward_2_action_block18
  · exact allFin _ _ backward_2_action_block19
  · exact allFin _ _ backward_2_action_block20
  · exact allFin _ _ backward_2_action_block21
  · exact allFin _ _ backward_2_action_block22
  · exact allFin _ _ backward_2_action_block23
  · exact allFin _ _ backward_2_action_block24
  · exact allFin _ _ backward_2_action_block25
  · exact allFin _ _ backward_2_action_block26
  · exact allFin _ _ backward_2_action_block27
  · exact allFin _ _ backward_2_action_block28
  · exact allFin _ _ backward_2_action_block29
  · exact allFin _ _ backward_2_action_block30
  · exact allFin _ _ backward_2_action_block31
  · exact allFin _ _ backward_2_action_block32

theorem backward_2 : conjugator * targetGenerator 2 * conjugator⁻¹ = evalSigned sourceGenerator (backwardWord 2) := Equiv.ext backward_2_action

abbrev forward_3_actionPredicate (x : Fin 2058) : Prop := (conjugator⁻¹ * sourceGenerator 3 * conjugator) x = (evalSigned targetGenerator (forwardWord 3)) x

private theorem forward_3_action_block0 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem forward_3_action_block1 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem forward_3_action_block2 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem forward_3_action_block3 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem forward_3_action_block4 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem forward_3_action_block5 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem forward_3_action_block6 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem forward_3_action_block7 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem forward_3_action_block8 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem forward_3_action_block9 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem forward_3_action_block10 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem forward_3_action_block11 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem forward_3_action_block12 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem forward_3_action_block13 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem forward_3_action_block14 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem forward_3_action_block15 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem forward_3_action_block16 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem forward_3_action_block17 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem forward_3_action_block18 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem forward_3_action_block19 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem forward_3_action_block20 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem forward_3_action_block21 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem forward_3_action_block22 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem forward_3_action_block23 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem forward_3_action_block24 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem forward_3_action_block25 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem forward_3_action_block26 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem forward_3_action_block27 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem forward_3_action_block28 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem forward_3_action_block29 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem forward_3_action_block30 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem forward_3_action_block31 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem forward_3_action_block32 : checkFin 64 (fun j => decide (forward_3_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem forward_3_action : ∀ x, forward_3_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ forward_3_action_block0
  · exact allFin _ _ forward_3_action_block1
  · exact allFin _ _ forward_3_action_block2
  · exact allFin _ _ forward_3_action_block3
  · exact allFin _ _ forward_3_action_block4
  · exact allFin _ _ forward_3_action_block5
  · exact allFin _ _ forward_3_action_block6
  · exact allFin _ _ forward_3_action_block7
  · exact allFin _ _ forward_3_action_block8
  · exact allFin _ _ forward_3_action_block9
  · exact allFin _ _ forward_3_action_block10
  · exact allFin _ _ forward_3_action_block11
  · exact allFin _ _ forward_3_action_block12
  · exact allFin _ _ forward_3_action_block13
  · exact allFin _ _ forward_3_action_block14
  · exact allFin _ _ forward_3_action_block15
  · exact allFin _ _ forward_3_action_block16
  · exact allFin _ _ forward_3_action_block17
  · exact allFin _ _ forward_3_action_block18
  · exact allFin _ _ forward_3_action_block19
  · exact allFin _ _ forward_3_action_block20
  · exact allFin _ _ forward_3_action_block21
  · exact allFin _ _ forward_3_action_block22
  · exact allFin _ _ forward_3_action_block23
  · exact allFin _ _ forward_3_action_block24
  · exact allFin _ _ forward_3_action_block25
  · exact allFin _ _ forward_3_action_block26
  · exact allFin _ _ forward_3_action_block27
  · exact allFin _ _ forward_3_action_block28
  · exact allFin _ _ forward_3_action_block29
  · exact allFin _ _ forward_3_action_block30
  · exact allFin _ _ forward_3_action_block31
  · exact allFin _ _ forward_3_action_block32

theorem forward_3 : conjugator⁻¹ * sourceGenerator 3 * conjugator = evalSigned targetGenerator (forwardWord 3) := Equiv.ext forward_3_action

abbrev backward_3_actionPredicate (x : Fin 2058) : Prop := (conjugator * targetGenerator 3 * conjugator⁻¹) x = (evalSigned sourceGenerator (backwardWord 3)) x

private theorem backward_3_action_block0 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 0 j.val))) = true := by decide +kernel
private theorem backward_3_action_block1 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 1 j.val))) = true := by decide +kernel
private theorem backward_3_action_block2 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 2 j.val))) = true := by decide +kernel
private theorem backward_3_action_block3 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 3 j.val))) = true := by decide +kernel
private theorem backward_3_action_block4 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 4 j.val))) = true := by decide +kernel
private theorem backward_3_action_block5 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 5 j.val))) = true := by decide +kernel
private theorem backward_3_action_block6 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 6 j.val))) = true := by decide +kernel
private theorem backward_3_action_block7 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 7 j.val))) = true := by decide +kernel
private theorem backward_3_action_block8 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 8 j.val))) = true := by decide +kernel
private theorem backward_3_action_block9 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 9 j.val))) = true := by decide +kernel
private theorem backward_3_action_block10 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 10 j.val))) = true := by decide +kernel
private theorem backward_3_action_block11 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 11 j.val))) = true := by decide +kernel
private theorem backward_3_action_block12 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 12 j.val))) = true := by decide +kernel
private theorem backward_3_action_block13 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 13 j.val))) = true := by decide +kernel
private theorem backward_3_action_block14 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 14 j.val))) = true := by decide +kernel
private theorem backward_3_action_block15 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 15 j.val))) = true := by decide +kernel
private theorem backward_3_action_block16 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 16 j.val))) = true := by decide +kernel
private theorem backward_3_action_block17 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 17 j.val))) = true := by decide +kernel
private theorem backward_3_action_block18 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 18 j.val))) = true := by decide +kernel
private theorem backward_3_action_block19 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 19 j.val))) = true := by decide +kernel
private theorem backward_3_action_block20 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 20 j.val))) = true := by decide +kernel
private theorem backward_3_action_block21 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 21 j.val))) = true := by decide +kernel
private theorem backward_3_action_block22 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 22 j.val))) = true := by decide +kernel
private theorem backward_3_action_block23 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 23 j.val))) = true := by decide +kernel
private theorem backward_3_action_block24 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 24 j.val))) = true := by decide +kernel
private theorem backward_3_action_block25 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 25 j.val))) = true := by decide +kernel
private theorem backward_3_action_block26 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 26 j.val))) = true := by decide +kernel
private theorem backward_3_action_block27 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 27 j.val))) = true := by decide +kernel
private theorem backward_3_action_block28 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 28 j.val))) = true := by decide +kernel
private theorem backward_3_action_block29 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 29 j.val))) = true := by decide +kernel
private theorem backward_3_action_block30 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 30 j.val))) = true := by decide +kernel
private theorem backward_3_action_block31 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 31 j.val))) = true := by decide +kernel
private theorem backward_3_action_block32 : checkFin 64 (fun j => decide (backward_3_actionPredicate (blockIndex 2058 64 (by decide) 32 j.val))) = true := by decide +kernel

theorem backward_3_action : ∀ x, backward_3_actionPredicate x := by
  apply allBlocks (b := 33) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ backward_3_action_block0
  · exact allFin _ _ backward_3_action_block1
  · exact allFin _ _ backward_3_action_block2
  · exact allFin _ _ backward_3_action_block3
  · exact allFin _ _ backward_3_action_block4
  · exact allFin _ _ backward_3_action_block5
  · exact allFin _ _ backward_3_action_block6
  · exact allFin _ _ backward_3_action_block7
  · exact allFin _ _ backward_3_action_block8
  · exact allFin _ _ backward_3_action_block9
  · exact allFin _ _ backward_3_action_block10
  · exact allFin _ _ backward_3_action_block11
  · exact allFin _ _ backward_3_action_block12
  · exact allFin _ _ backward_3_action_block13
  · exact allFin _ _ backward_3_action_block14
  · exact allFin _ _ backward_3_action_block15
  · exact allFin _ _ backward_3_action_block16
  · exact allFin _ _ backward_3_action_block17
  · exact allFin _ _ backward_3_action_block18
  · exact allFin _ _ backward_3_action_block19
  · exact allFin _ _ backward_3_action_block20
  · exact allFin _ _ backward_3_action_block21
  · exact allFin _ _ backward_3_action_block22
  · exact allFin _ _ backward_3_action_block23
  · exact allFin _ _ backward_3_action_block24
  · exact allFin _ _ backward_3_action_block25
  · exact allFin _ _ backward_3_action_block26
  · exact allFin _ _ backward_3_action_block27
  · exact allFin _ _ backward_3_action_block28
  · exact allFin _ _ backward_3_action_block29
  · exact allFin _ _ backward_3_action_block30
  · exact allFin _ _ backward_3_action_block31
  · exact allFin _ _ backward_3_action_block32

theorem backward_3 : conjugator * targetGenerator 3 * conjugator⁻¹ = evalSigned sourceGenerator (backwardWord 3) := Equiv.ext backward_3_action

theorem card_eq : Nat.card (Subgroup.closure (Set.range sourceGenerator)) =
    Nat.card (Subgroup.closure (Set.range targetGenerator)) := by
  apply card_closure_equiv (MulAut.conj conjugator⁻¹)
  · intro k
    have h : conjugator⁻¹ * sourceGenerator k * conjugator =
        evalSigned targetGenerator (forwardWord k) := by
      fin_cases k
      · exact forward_0
      · exact forward_1
      · exact forward_2
      · exact forward_3
    change conjugator⁻¹ * sourceGenerator k * (conjugator⁻¹)⁻¹ ∈ _
    rw [inv_inv, h]
    exact evalSigned_mem _ _ _ (fun j => Subgroup.subset_closure (Set.mem_range_self j))
  · intro k
    have h : conjugator * targetGenerator k * conjugator⁻¹ =
        evalSigned sourceGenerator (backwardWord k) := by
      fin_cases k
      · exact backward_0
      · exact backward_1
      · exact backward_2
      · exact backward_3
    change (conjugator⁻¹)⁻¹ * targetGenerator k * conjugator⁻¹ ∈ _
    rw [inv_inv, h]
    exact evalSigned_mem _ _ _ (fun j => Subgroup.subset_closure (Set.mem_range_self j))

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair10Conjugacy
