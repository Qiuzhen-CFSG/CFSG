module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Data
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.InvolutionFibers.Data
import Mathlib.Tactic.FinCases

/-! Finite first-class bridges in the literal max1 binary coordinates.
The untrusted search supplies only witnesses. All orbit labels and bridge
identities below are checked by Lean's kernel, using the previously certified
ATLAS local actions. Source: Kleidman--Wilson (1988), p.487, Corollary 1.1.4. -/

@[expose] public section
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf.PureSecondData
open Janko4.Cardinality.KernelCount Janko4.Cardinality.QuotientCount.Image
open Janko4.Simplicity.Max1Fusion

/-- The root of the existing certified kernel-orbit forest. -/
def orbitRoot (m : ℕ) : ℕ :=
  if m < 1024 then
    if m < 512 then
      if m < 256 then
        if m < 128 then
          if m < 64 then
            if m < 32 then
              if m < 16 then
                if m < 8 then
                  if m < 4 then
                    if m < 2 then
                      if m < 1 then
                        0
                      else
                        1
                    else
                      if m < 3 then
                        1
                      else
                        3
                  else
                    if m < 6 then
                      if m < 5 then
                        1
                      else
                        3
                    else
                      3
                else
                  if m < 12 then
                    if m < 10 then
                      if m < 9 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
              else
                if m < 24 then
                  if m < 20 then
                    if m < 18 then
                      if m < 17 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 28 then
                    3
                  else
                    1
            else
              if m < 48 then
                if m < 40 then
                  if m < 36 then
                    if m < 34 then
                      if m < 33 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 44 then
                    if m < 42 then
                      if m < 41 then
                        3
                      else
                        1
                    else
                      if m < 43 then
                        3
                      else
                        1
                  else
                    if m < 46 then
                      if m < 45 then
                        3
                      else
                        1
                    else
                      if m < 47 then
                        3
                      else
                        1
              else
                if m < 56 then
                  if m < 52 then
                    if m < 50 then
                      3
                    else
                      1
                  else
                    if m < 54 then
                      3
                    else
                      1
                else
                  3
          else
            if m < 96 then
              if m < 80 then
                if m < 72 then
                  if m < 68 then
                    if m < 66 then
                      if m < 65 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 70 then
                      3
                    else
                      1
                else
                  if m < 76 then
                    3
                  else
                    if m < 78 then
                      3
                    else
                      1
              else
                if m < 88 then
                  if m < 84 then
                    if m < 82 then
                      if m < 81 then
                        3
                      else
                        1
                    else
                      if m < 83 then
                        3
                      else
                        1
                  else
                    3
                else
                  if m < 92 then
                    if m < 90 then
                      if m < 89 then
                        3
                      else
                        1
                    else
                      if m < 91 then
                        3
                      else
                        1
                  else
                    3
            else
              if m < 112 then
                3
              else
                if m < 120 then
                  if m < 116 then
                    if m < 114 then
                      if m < 113 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 118 then
                      if m < 117 then
                        1
                      else
                        3
                    else
                      3
                else
                  if m < 124 then
                    if m < 122 then
                      if m < 121 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 126 then
                      if m < 125 then
                        1
                      else
                        3
                    else
                      if m < 127 then
                        3
                      else
                        1
        else
          if m < 192 then
            if m < 160 then
              if m < 144 then
                if m < 136 then
                  if m < 132 then
                    if m < 130 then
                      if m < 129 then
                        1
                      else
                        3
                    else
                      if m < 131 then
                        3
                      else
                        1
                  else
                    if m < 134 then
                      3
                    else
                      if m < 135 then
                        3
                      else
                        1
                else
                  3
              else
                if m < 152 then
                  if m < 148 then
                    if m < 146 then
                      3
                    else
                      if m < 147 then
                        3
                      else
                        1
                  else
                    if m < 150 then
                      3
                    else
                      if m < 151 then
                        3
                      else
                        1
                else
                  3
            else
              if m < 176 then
                if m < 168 then
                  if m < 164 then
                    3
                  else
                    if m < 166 then
                      1
                    else
                      3
                else
                  if m < 172 then
                    if m < 170 then
                      if m < 169 then
                        1
                      else
                        3
                    else
                      if m < 171 then
                        1
                      else
                        3
                  else
                    3
              else
                if m < 184 then
                  if m < 180 then
                    3
                  else
                    if m < 182 then
                      1
                    else
                      3
                else
                  if m < 188 then
                    if m < 186 then
                      if m < 185 then
                        1
                      else
                        3
                    else
                      if m < 187 then
                        1
                      else
                        3
                  else
                    if m < 190 then
                      3
                    else
                      if m < 191 then
                        3
                      else
                        1
          else
            if m < 224 then
              if m < 208 then
                3
              else
                if m < 216 then
                  3
                else
                  if m < 220 then
                    3
                  else
                    if m < 222 then
                      3
                    else
                      if m < 223 then
                        3
                      else
                        1
            else
              if m < 240 then
                if m < 232 then
                  if m < 228 then
                    if m < 226 then
                      if m < 225 then
                        1
                      else
                        3
                    else
                      if m < 227 then
                        3
                      else
                        1
                  else
                    3
                else
                  if m < 236 then
                    if m < 234 then
                      3
                    else
                      if m < 235 then
                        3
                      else
                        1
                  else
                    3
              else
                if m < 248 then
                  if m < 244 then
                    if m < 242 then
                      3
                    else
                      if m < 243 then
                        3
                      else
                        1
                  else
                    3
                else
                  if m < 252 then
                    if m < 250 then
                      3
                    else
                      if m < 251 then
                        3
                      else
                        1
                  else
                    3
      else
        if m < 384 then
          if m < 320 then
            if m < 288 then
              if m < 272 then
                if m < 264 then
                  if m < 260 then
                    if m < 258 then
                      if m < 257 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 262 then
                      if m < 261 then
                        3
                      else
                        1
                    else
                      if m < 263 then
                        3
                      else
                        1
                else
                  if m < 268 then
                    if m < 266 then
                      3
                    else
                      if m < 267 then
                        1
                      else
                        3
                  else
                    if m < 270 then
                      3
                    else
                      if m < 271 then
                        1
                      else
                        3
              else
                if m < 280 then
                  3
                else
                  if m < 284 then
                    if m < 282 then
                      1
                    else
                      3
                  else
                    3
            else
              if m < 304 then
                if m < 296 then
                  if m < 292 then
                    3
                  else
                    if m < 294 then
                      if m < 293 then
                        3
                      else
                        1
                    else
                      if m < 295 then
                        3
                      else
                        1
                else
                  if m < 300 then
                    if m < 298 then
                      3
                    else
                      if m < 299 then
                        1
                      else
                        3
                  else
                    if m < 302 then
                      3
                    else
                      if m < 303 then
                        1
                      else
                        3
              else
                if m < 312 then
                  3
                else
                  if m < 316 then
                    if m < 314 then
                      1
                    else
                      3
                  else
                    if m < 318 then
                      3
                    else
                      if m < 319 then
                        3
                      else
                        1
          else
            if m < 352 then
              if m < 336 then
                3
              else
                if m < 344 then
                  if m < 340 then
                    if m < 338 then
                      if m < 337 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 342 then
                      3
                    else
                      if m < 343 then
                        1
                      else
                        3
                else
                  if m < 348 then
                    3
                  else
                    if m < 350 then
                      3
                    else
                      if m < 351 then
                        1
                      else
                        3
            else
              if m < 368 then
                if m < 360 then
                  3
                else
                  if m < 364 then
                    3
                  else
                    if m < 366 then
                      3
                    else
                      if m < 367 then
                        3
                      else
                        1
              else
                if m < 376 then
                  if m < 372 then
                    3
                  else
                    if m < 374 then
                      3
                    else
                      if m < 375 then
                        1
                      else
                        3
                else
                  if m < 380 then
                    3
                  else
                    if m < 382 then
                      3
                    else
                      if m < 383 then
                        1
                      else
                        3
        else
          if m < 448 then
            if m < 416 then
              if m < 400 then
                if m < 392 then
                  3
                else
                  if m < 396 then
                    if m < 394 then
                      if m < 393 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 398 then
                      if m < 397 then
                        3
                      else
                        1
                    else
                      3
              else
                if m < 408 then
                  3
                else
                  if m < 412 then
                    3
                  else
                    if m < 414 then
                      if m < 413 then
                        3
                      else
                        1
                    else
                      3
            else
              if m < 432 then
                if m < 424 then
                  3
                else
                  if m < 428 then
                    3
                  else
                    if m < 430 then
                      if m < 429 then
                        3
                      else
                        1
                    else
                      3
              else
                if m < 440 then
                  if m < 436 then
                    3
                  else
                    if m < 438 then
                      3
                    else
                      if m < 439 then
                        3
                      else
                        1
                else
                  if m < 444 then
                    3
                  else
                    if m < 446 then
                      if m < 445 then
                        3
                      else
                        1
                    else
                      3
          else
            if m < 480 then
              if m < 464 then
                if m < 456 then
                  3
                else
                  if m < 460 then
                    if m < 458 then
                      if m < 457 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
              else
                if m < 472 then
                  if m < 468 then
                    if m < 466 then
                      if m < 465 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 476 then
                    3
                  else
                    if m < 478 then
                      3
                    else
                      if m < 479 then
                        3
                      else
                        1
            else
              if m < 496 then
                if m < 488 then
                  if m < 484 then
                    if m < 482 then
                      if m < 481 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 492 then
                    3
                  else
                    if m < 494 then
                      3
                    else
                      if m < 495 then
                        3
                      else
                        1
              else
                if m < 504 then
                  if m < 500 then
                    3
                  else
                    if m < 502 then
                      3
                    else
                      if m < 503 then
                        3
                      else
                        1
                else
                  3
    else
      if m < 768 then
        if m < 640 then
          if m < 576 then
            if m < 544 then
              if m < 528 then
                if m < 520 then
                  if m < 516 then
                    if m < 514 then
                      if m < 513 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 518 then
                      if m < 517 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 524 then
                    if m < 522 then
                      3
                    else
                      1
                  else
                    if m < 526 then
                      if m < 525 then
                        3
                      else
                        1
                    else
                      3
              else
                if m < 536 then
                  if m < 532 then
                    3
                  else
                    if m < 534 then
                      if m < 533 then
                        1
                      else
                        3
                    else
                      if m < 535 then
                        1
                      else
                        3
                else
                  3
            else
              if m < 560 then
                3
              else
                if m < 568 then
                  if m < 564 then
                    if m < 562 then
                      if m < 561 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 572 then
                    if m < 570 then
                      if m < 569 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 574 then
                      if m < 573 then
                        3
                      else
                        1
                    else
                      3
          else
            if m < 608 then
              if m < 592 then
                if m < 584 then
                  if m < 580 then
                    3
                  else
                    if m < 582 then
                      if m < 581 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 588 then
                    if m < 586 then
                      3
                    else
                      1
                  else
                    if m < 590 then
                      if m < 589 then
                        3
                      else
                        1
                    else
                      3
              else
                if m < 600 then
                  if m < 596 then
                    3
                  else
                    if m < 598 then
                      if m < 597 then
                        1
                      else
                        3
                    else
                      if m < 599 then
                        1
                      else
                        3
                else
                  if m < 604 then
                    3
                  else
                    if m < 606 then
                      3
                    else
                      if m < 607 then
                        3
                      else
                        1
            else
              if m < 624 then
                if m < 616 then
                  3
                else
                  if m < 620 then
                    3
                  else
                    if m < 622 then
                      3
                    else
                      if m < 623 then
                        3
                      else
                        1
              else
                if m < 632 then
                  3
                else
                  if m < 636 then
                    if m < 634 then
                      if m < 633 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 638 then
                      if m < 637 then
                        3
                      else
                        1
                    else
                      3
        else
          if m < 704 then
            if m < 672 then
              if m < 656 then
                if m < 648 then
                  if m < 644 then
                    if m < 642 then
                      if m < 641 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 652 then
                    3
                  else
                    if m < 654 then
                      3
                    else
                      if m < 655 then
                        3
                      else
                        1
              else
                if m < 664 then
                  3
                else
                  if m < 668 then
                    if m < 666 then
                      3
                    else
                      if m < 667 then
                        3
                      else
                        1
                  else
                    3
            else
              if m < 688 then
                if m < 680 then
                  3
                else
                  if m < 684 then
                    3
                  else
                    if m < 686 then
                      3
                    else
                      if m < 687 then
                        1
                      else
                        3
              else
                if m < 696 then
                  3
                else
                  if m < 700 then
                    if m < 698 then
                      3
                    else
                      if m < 699 then
                        3
                      else
                        1
                  else
                    if m < 702 then
                      3
                    else
                      if m < 703 then
                        1
                      else
                        3
          else
            if m < 736 then
              if m < 720 then
                if m < 712 then
                  if m < 708 then
                    3
                  else
                    if m < 710 then
                      if m < 709 then
                        1
                      else
                        3
                    else
                      3
                else
                  3
              else
                if m < 728 then
                  if m < 724 then
                    if m < 722 then
                      if m < 721 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 732 then
                    3
                  else
                    if m < 734 then
                      3
                    else
                      if m < 735 then
                        3
                      else
                        1
            else
              if m < 752 then
                if m < 744 then
                  if m < 740 then
                    3
                  else
                    if m < 742 then
                      if m < 741 then
                        1
                      else
                        3
                    else
                      3
                else
                  if m < 748 then
                    3
                  else
                    if m < 750 then
                      3
                    else
                      if m < 751 then
                        1
                      else
                        3
              else
                if m < 760 then
                  3
                else
                  if m < 764 then
                    3
                  else
                    if m < 766 then
                      3
                    else
                      if m < 767 then
                        1
                      else
                        3
      else
        if m < 896 then
          if m < 832 then
            if m < 800 then
              if m < 784 then
                3
              else
                if m < 792 then
                  if m < 788 then
                    if m < 786 then
                      3
                    else
                      if m < 787 then
                        3
                      else
                        1
                  else
                    3
                else
                  3
            else
              if m < 816 then
                if m < 808 then
                  if m < 804 then
                    3
                  else
                    if m < 806 then
                      3
                    else
                      if m < 807 then
                        1
                      else
                        3
                else
                  3
              else
                if m < 824 then
                  if m < 820 then
                    if m < 818 then
                      if m < 817 then
                        1
                      else
                        3
                    else
                      if m < 819 then
                        3
                      else
                        1
                  else
                    if m < 822 then
                      3
                    else
                      if m < 823 then
                        1
                      else
                        3
                else
                  if m < 828 then
                    3
                  else
                    if m < 830 then
                      3
                    else
                      if m < 831 then
                        3
                      else
                        1
          else
            if m < 864 then
              if m < 848 then
                if m < 840 then
                  3
                else
                  if m < 844 then
                    if m < 842 then
                      if m < 841 then
                        3
                      else
                        1
                    else
                      3
                  else
                    3
              else
                if m < 856 then
                  if m < 852 then
                    if m < 850 then
                      if m < 849 then
                        1
                      else
                        3
                    else
                      if m < 851 then
                        3
                      else
                        1
                  else
                    3
                else
                  if m < 860 then
                    if m < 858 then
                      if m < 857 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 862 then
                      3
                    else
                      if m < 863 then
                        3
                      else
                        1
            else
              if m < 880 then
                3
              else
                if m < 888 then
                  if m < 884 then
                    if m < 882 then
                      3
                    else
                      if m < 883 then
                        3
                      else
                        1
                  else
                    3
                else
                  3
        else
          if m < 960 then
            if m < 928 then
              if m < 912 then
                if m < 904 then
                  if m < 900 then
                    if m < 898 then
                      3
                    else
                      1
                  else
                    3
                else
                  if m < 908 then
                    3
                  else
                    if m < 910 then
                      3
                    else
                      if m < 911 then
                        3
                      else
                        1
              else
                if m < 920 then
                  3
                else
                  if m < 924 then
                    3
                  else
                    if m < 926 then
                      if m < 925 then
                        1
                      else
                        3
                    else
                      if m < 927 then
                        1
                      else
                        3
            else
              if m < 944 then
                3
              else
                if m < 952 then
                  if m < 948 then
                    if m < 946 then
                      if m < 945 then
                        3
                      else
                        1
                    else
                      if m < 947 then
                        1
                      else
                        3
                  else
                    if m < 950 then
                      if m < 949 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 956 then
                    if m < 954 then
                      3
                    else
                      if m < 955 then
                        1
                      else
                        3
                  else
                    if m < 958 then
                      3
                    else
                      if m < 959 then
                        3
                      else
                        1
          else
            if m < 992 then
              if m < 976 then
                if m < 968 then
                  if m < 964 then
                    3
                  else
                    if m < 966 then
                      if m < 965 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 972 then
                    if m < 970 then
                      3
                    else
                      if m < 971 then
                        1
                      else
                        3
                  else
                    if m < 974 then
                      if m < 973 then
                        3
                      else
                        1
                    else
                      if m < 975 then
                        1
                      else
                        3
              else
                if m < 984 then
                  3
                else
                  if m < 988 then
                    3
                  else
                    if m < 990 then
                      3
                    else
                      if m < 991 then
                        3
                      else
                        1
            else
              if m < 1008 then
                if m < 1000 then
                  if m < 996 then
                    if m < 994 then
                      if m < 993 then
                        3
                      else
                        1
                    else
                      if m < 995 then
                        3
                      else
                        1
                  else
                    3
                else
                  if m < 1004 then
                    3
                  else
                    if m < 1006 then
                      3
                    else
                      if m < 1007 then
                        3
                      else
                        1
              else
                if m < 1016 then
                  3
                else
                  if m < 1020 then
                    3
                  else
                    if m < 1022 then
                      1
                    else
                      3
  else
    if m < 1536 then
      if m < 1280 then
        if m < 1152 then
          if m < 1088 then
            if m < 1056 then
              if m < 1040 then
                if m < 1032 then
                  if m < 1028 then
                    if m < 1026 then
                      if m < 1025 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 1030 then
                      3
                    else
                      if m < 1031 then
                        1
                      else
                        3
                else
                  3
              else
                if m < 1048 then
                  if m < 1044 then
                    if m < 1042 then
                      if m < 1041 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 1046 then
                      if m < 1045 then
                        3
                      else
                        1
                    else
                      if m < 1047 then
                        1
                      else
                        3
                else
                  3
            else
              if m < 1072 then
                if m < 1064 then
                  if m < 1060 then
                    if m < 1058 then
                      3
                    else
                      1
                  else
                    3
                else
                  if m < 1068 then
                    if m < 1066 then
                      if m < 1065 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
              else
                if m < 1080 then
                  3
                else
                  if m < 1084 then
                    3
                  else
                    if m < 1086 then
                      if m < 1085 then
                        1
                      else
                        3
                    else
                      if m < 1087 then
                        1
                      else
                        3
          else
            if m < 1120 then
              if m < 1104 then
                if m < 1096 then
                  3
                else
                  if m < 1100 then
                    if m < 1098 then
                      3
                    else
                      if m < 1099 then
                        3
                      else
                        1
                  else
                    3
              else
                3
            else
              if m < 1136 then
                if m < 1128 then
                  if m < 1124 then
                    3
                  else
                    if m < 1126 then
                      if m < 1125 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 1132 then
                    if m < 1130 then
                      if m < 1129 then
                        1
                      else
                        3
                    else
                      if m < 1131 then
                        3
                      else
                        1
                  else
                    if m < 1134 then
                      if m < 1133 then
                        3
                      else
                        1
                    else
                      3
              else
                if m < 1144 then
                  3
                else
                  if m < 1148 then
                    3
                  else
                    if m < 1150 then
                      3
                    else
                      if m < 1151 then
                        3
                      else
                        1
        else
          if m < 1216 then
            if m < 1184 then
              if m < 1168 then
                if m < 1160 then
                  if m < 1156 then
                    3
                  else
                    if m < 1158 then
                      3
                    else
                      if m < 1159 then
                        1
                      else
                        3
                else
                  3
              else
                if m < 1176 then
                  if m < 1172 then
                    if m < 1170 then
                      if m < 1169 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 1174 then
                      if m < 1173 then
                        3
                      else
                        1
                    else
                      if m < 1175 then
                        1
                      else
                        3
                else
                  if m < 1180 then
                    3
                  else
                    if m < 1182 then
                      3
                    else
                      if m < 1183 then
                        3
                      else
                        1
            else
              if m < 1200 then
                if m < 1192 then
                  if m < 1188 then
                    if m < 1186 then
                      3
                    else
                      1
                  else
                    3
                else
                  3
              else
                if m < 1208 then
                  if m < 1204 then
                    3
                  else
                    if m < 1206 then
                      3
                    else
                      if m < 1207 then
                        3
                      else
                        1
                else
                  if m < 1212 then
                    3
                  else
                    if m < 1214 then
                      if m < 1213 then
                        1
                      else
                        3
                    else
                      if m < 1215 then
                        1
                      else
                        3
          else
            if m < 1248 then
              if m < 1232 then
                3
              else
                if m < 1240 then
                  if m < 1236 then
                    3
                  else
                    if m < 1238 then
                      if m < 1237 then
                        1
                      else
                        3
                    else
                      3
                else
                  3
            else
              if m < 1264 then
                if m < 1256 then
                  if m < 1252 then
                    if m < 1250 then
                      if m < 1249 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 1254 then
                      if m < 1253 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 1260 then
                    3
                  else
                    if m < 1262 then
                      if m < 1261 then
                        3
                      else
                        1
                    else
                      3
              else
                if m < 1272 then
                  if m < 1268 then
                    3
                  else
                    if m < 1270 then
                      if m < 1269 then
                        1
                      else
                        3
                    else
                      if m < 1271 then
                        3
                      else
                        1
                else
                  3
      else
        if m < 1408 then
          if m < 1344 then
            if m < 1312 then
              if m < 1296 then
                if m < 1288 then
                  if m < 1284 then
                    if m < 1282 then
                      if m < 1281 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  3
              else
                if m < 1304 then
                  if m < 1300 then
                    3
                  else
                    if m < 1302 then
                      3
                    else
                      if m < 1303 then
                        3
                      else
                        1
                else
                  if m < 1308 then
                    if m < 1306 then
                      3
                    else
                      if m < 1307 then
                        3
                      else
                        1
                  else
                    3
            else
              if m < 1328 then
                3
              else
                if m < 1336 then
                  if m < 1332 then
                    3
                  else
                    if m < 1334 then
                      if m < 1333 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 1340 then
                    if m < 1338 then
                      3
                    else
                      if m < 1339 then
                        3
                      else
                        1
                  else
                    if m < 1342 then
                      if m < 1341 then
                        3
                      else
                        1
                    else
                      3
          else
            if m < 1376 then
              if m < 1360 then
                if m < 1352 then
                  if m < 1348 then
                    if m < 1346 then
                      if m < 1345 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 1350 then
                      if m < 1349 then
                        3
                      else
                        1
                    else
                      3
                else
                  3
              else
                if m < 1368 then
                  if m < 1364 then
                    3
                  else
                    if m < 1366 then
                      3
                    else
                      if m < 1367 then
                        3
                      else
                        1
                else
                  3
            else
              if m < 1392 then
                if m < 1384 then
                  3
                else
                  if m < 1388 then
                    if m < 1386 then
                      if m < 1385 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 1390 then
                      if m < 1389 then
                        1
                      else
                        3
                    else
                      if m < 1391 then
                        1
                      else
                        3
              else
                if m < 1400 then
                  if m < 1396 then
                    if m < 1394 then
                      3
                    else
                      1
                  else
                    3
                else
                  if m < 1404 then
                    if m < 1402 then
                      if m < 1401 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 1406 then
                      3
                    else
                      if m < 1407 then
                        3
                      else
                        1
        else
          if m < 1472 then
            if m < 1440 then
              if m < 1424 then
                if m < 1416 then
                  if m < 1412 then
                    if m < 1410 then
                      3
                    else
                      if m < 1411 then
                        1
                      else
                        3
                  else
                    3
                else
                  if m < 1420 then
                    if m < 1418 then
                      3
                    else
                      if m < 1419 then
                        1
                      else
                        3
                  else
                    3
              else
                if m < 1432 then
                  3
                else
                  if m < 1436 then
                    if m < 1434 then
                      3
                    else
                      if m < 1435 then
                        3
                      else
                        1
                  else
                    3
            else
              if m < 1456 then
                if m < 1448 then
                  if m < 1444 then
                    if m < 1442 then
                      if m < 1441 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  3
              else
                if m < 1464 then
                  if m < 1460 then
                    3
                  else
                    if m < 1462 then
                      3
                    else
                      if m < 1463 then
                        3
                      else
                        1
                else
                  if m < 1468 then
                    if m < 1466 then
                      3
                    else
                      if m < 1467 then
                        3
                      else
                        1
                  else
                    3
          else
            if m < 1504 then
              if m < 1488 then
                if m < 1480 then
                  if m < 1476 then
                    3
                  else
                    if m < 1478 then
                      3
                    else
                      if m < 1479 then
                        1
                      else
                        3
                else
                  if m < 1484 then
                    3
                  else
                    if m < 1486 then
                      1
                    else
                      3
              else
                if m < 1496 then
                  if m < 1492 then
                    if m < 1490 then
                      if m < 1489 then
                        3
                      else
                        1
                    else
                      if m < 1491 then
                        3
                      else
                        1
                  else
                    if m < 1494 then
                      3
                    else
                      if m < 1495 then
                        1
                      else
                        3
                else
                  if m < 1500 then
                    3
                  else
                    if m < 1502 then
                      3
                    else
                      if m < 1503 then
                        3
                      else
                        1
            else
              if m < 1520 then
                3
              else
                if m < 1528 then
                  if m < 1524 then
                    3
                  else
                    if m < 1526 then
                      3
                    else
                      if m < 1527 then
                        3
                      else
                        1
                else
                  if m < 1532 then
                    if m < 1530 then
                      3
                    else
                      if m < 1531 then
                        1
                      else
                        3
                  else
                    if m < 1534 then
                      3
                    else
                      if m < 1535 then
                        1
                      else
                        3
    else
      if m < 1792 then
        if m < 1664 then
          if m < 1600 then
            if m < 1568 then
              if m < 1552 then
                if m < 1544 then
                  if m < 1540 then
                    3
                  else
                    if m < 1542 then
                      if m < 1541 then
                        1
                      else
                        3
                    else
                      3
                else
                  3
              else
                if m < 1560 then
                  if m < 1556 then
                    if m < 1554 then
                      if m < 1553 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 1558 then
                      if m < 1557 then
                        3
                      else
                        1
                    else
                      3
                else
                  3
            else
              if m < 1584 then
                if m < 1576 then
                  if m < 1572 then
                    if m < 1570 then
                      3
                    else
                      1
                  else
                    if m < 1574 then
                      if m < 1573 then
                        1
                      else
                        3
                    else
                      3
                else
                  if m < 1580 then
                    if m < 1578 then
                      if m < 1577 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
              else
                if m < 1592 then
                  if m < 1588 then
                    if m < 1586 then
                      if m < 1585 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 1596 then
                    3
                  else
                    if m < 1598 then
                      if m < 1597 then
                        1
                      else
                        3
                    else
                      if m < 1599 then
                        1
                      else
                        3
          else
            if m < 1632 then
              if m < 1616 then
                if m < 1608 then
                  3
                else
                  if m < 1612 then
                    if m < 1610 then
                      if m < 1609 then
                        3
                      else
                        1
                    else
                      3
                  else
                    if m < 1614 then
                      3
                    else
                      if m < 1615 then
                        3
                      else
                        1
              else
                if m < 1624 then
                  3
                else
                  if m < 1628 then
                    if m < 1626 then
                      if m < 1625 then
                        3
                      else
                        1
                    else
                      3
                  else
                    3
            else
              if m < 1648 then
                if m < 1640 then
                  if m < 1636 then
                    3
                  else
                    if m < 1638 then
                      if m < 1637 then
                        3
                      else
                        1
                    else
                      3
                else
                  if m < 1644 then
                    if m < 1642 then
                      if m < 1641 then
                        1
                      else
                        3
                    else
                      3
                  else
                    if m < 1646 then
                      if m < 1645 then
                        3
                      else
                        1
                    else
                      3
              else
                3
        else
          if m < 1728 then
            if m < 1696 then
              if m < 1680 then
                if m < 1672 then
                  if m < 1668 then
                    3
                  else
                    if m < 1670 then
                      3
                    else
                      if m < 1671 then
                        1
                      else
                        3
                else
                  if m < 1676 then
                    3
                  else
                    if m < 1678 then
                      3
                    else
                      if m < 1679 then
                        3
                      else
                        1
              else
                if m < 1688 then
                  if m < 1684 then
                    3
                  else
                    if m < 1686 then
                      3
                    else
                      if m < 1687 then
                        1
                      else
                        3
                else
                  3
            else
              if m < 1712 then
                if m < 1704 then
                  3
                else
                  if m < 1708 then
                    if m < 1706 then
                      if m < 1705 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
              else
                if m < 1720 then
                  if m < 1716 then
                    if m < 1714 then
                      3
                    else
                      if m < 1715 then
                        1
                      else
                        3
                  else
                    3
                else
                  if m < 1724 then
                    if m < 1722 then
                      3
                    else
                      if m < 1723 then
                        1
                      else
                        3
                  else
                    3
          else
            if m < 1760 then
              if m < 1744 then
                if m < 1736 then
                  if m < 1732 then
                    3
                  else
                    if m < 1734 then
                      if m < 1733 then
                        1
                      else
                        3
                    else
                      3
                else
                  if m < 1740 then
                    if m < 1738 then
                      3
                    else
                      if m < 1739 then
                        1
                      else
                        3
                  else
                    if m < 1742 then
                      3
                    else
                      if m < 1743 then
                        1
                      else
                        3
              else
                3
            else
              if m < 1776 then
                if m < 1768 then
                  if m < 1764 then
                    if m < 1762 then
                      if m < 1761 then
                        3
                      else
                        1
                    else
                      if m < 1763 then
                        3
                      else
                        1
                  else
                    if m < 1766 then
                      if m < 1765 then
                        1
                      else
                        3
                    else
                      3
                else
                  if m < 1772 then
                    if m < 1770 then
                      if m < 1769 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
              else
                if m < 1784 then
                  if m < 1780 then
                    if m < 1778 then
                      if m < 1777 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 1788 then
                    3
                  else
                    if m < 1790 then
                      1
                    else
                      3
      else
        if m < 1920 then
          if m < 1856 then
            if m < 1824 then
              if m < 1808 then
                if m < 1800 then
                  if m < 1796 then
                    if m < 1794 then
                      if m < 1793 then
                        3
                      else
                        1
                    else
                      if m < 1795 then
                        3
                      else
                        1
                  else
                    3
                else
                  3
              else
                if m < 1816 then
                  3
                else
                  if m < 1820 then
                    if m < 1818 then
                      3
                    else
                      if m < 1819 then
                        3
                      else
                        1
                  else
                    if m < 1822 then
                      1
                    else
                      3
            else
              if m < 1840 then
                if m < 1832 then
                  if m < 1828 then
                    if m < 1826 then
                      if m < 1825 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 1836 then
                    if m < 1834 then
                      3
                    else
                      if m < 1835 then
                        1
                      else
                        3
                  else
                    if m < 1838 then
                      3
                    else
                      if m < 1839 then
                        1
                      else
                        3
              else
                if m < 1848 then
                  3
                else
                  if m < 1852 then
                    if m < 1850 then
                      if m < 1849 then
                        1
                      else
                        3
                    else
                      if m < 1851 then
                        3
                      else
                        1
                  else
                    3
          else
            if m < 1888 then
              if m < 1872 then
                if m < 1864 then
                  3
                else
                  if m < 1868 then
                    if m < 1866 then
                      if m < 1865 then
                        3
                      else
                        1
                    else
                      3
                  else
                    3
              else
                if m < 1880 then
                  if m < 1876 then
                    if m < 1874 then
                      3
                    else
                      if m < 1875 then
                        1
                      else
                        3
                  else
                    3
                else
                  if m < 1884 then
                    if m < 1882 then
                      if m < 1881 then
                        3
                      else
                        1
                    else
                      if m < 1883 then
                        1
                      else
                        3
                  else
                    if m < 1886 then
                      3
                    else
                      if m < 1887 then
                        3
                      else
                        1
            else
              if m < 1904 then
                3
              else
                if m < 1912 then
                  3
                else
                  if m < 1916 then
                    if m < 1914 then
                      if m < 1913 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
        else
          if m < 1984 then
            if m < 1952 then
              if m < 1936 then
                if m < 1928 then
                  if m < 1924 then
                    3
                  else
                    if m < 1926 then
                      3
                    else
                      if m < 1927 then
                        3
                      else
                        1
                else
                  3
              else
                3
            else
              if m < 1968 then
                if m < 1960 then
                  if m < 1956 then
                    if m < 1954 then
                      if m < 1953 then
                        1
                      else
                        3
                    else
                      3
                  else
                    3
                else
                  if m < 1964 then
                    if m < 1962 then
                      if m < 1961 then
                        3
                      else
                        1
                    else
                      3
                  else
                    3
              else
                if m < 1976 then
                  if m < 1972 then
                    if m < 1970 then
                      3
                    else
                      if m < 1971 then
                        1
                      else
                        3
                  else
                    3
                else
                  if m < 1980 then
                    if m < 1978 then
                      if m < 1977 then
                        3
                      else
                        1
                    else
                      if m < 1979 then
                        1
                      else
                        3
                  else
                    3
          else
            if m < 2016 then
              if m < 2000 then
                if m < 1992 then
                  if m < 1988 then
                    3
                  else
                    if m < 1990 then
                      if m < 1989 then
                        1
                      else
                        3
                    else
                      if m < 1991 then
                        3
                      else
                        1
                else
                  if m < 1996 then
                    if m < 1994 then
                      3
                    else
                      if m < 1995 then
                        1
                      else
                        3
                  else
                    if m < 1998 then
                      3
                    else
                      if m < 1999 then
                        1
                      else
                        3
              else
                if m < 2008 then
                  3
                else
                  if m < 2012 then
                    3
                  else
                    if m < 2014 then
                      3
                    else
                      if m < 2015 then
                        3
                      else
                        1
            else
              if m < 2032 then
                if m < 2024 then
                  if m < 2020 then
                    if m < 2018 then
                      if m < 2017 then
                        3
                      else
                        1
                    else
                      if m < 2019 then
                        3
                      else
                        1
                  else
                    if m < 2022 then
                      if m < 2021 then
                        1
                      else
                        3
                    else
                      3
                else
                  3
              else
                if m < 2040 then
                  3
                else
                  if m < 2044 then
                    3
                  else
                    if m < 2046 then
                      1
                    else
                      3

def RootValid (m : Fin 2048) : Prop :=
  (orbitRoot m.val = 0 ∨ orbitRoot m.val = 1 ∨ orbitRoot m.val = 3) ∧
  (orbitRoot m.val = 0 ↔ m = 0) ∧
  orbitRoot (KernelOrbits.parent m).val = orbitRoot m.val

instance (m : Fin 2048) : Decidable (RootValid m) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem rootBlock0 : ∀ i : Fin 64, RootValid ⟨0 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock1 : ∀ i : Fin 64, RootValid ⟨64 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock2 : ∀ i : Fin 64, RootValid ⟨128 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock3 : ∀ i : Fin 64, RootValid ⟨192 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock4 : ∀ i : Fin 64, RootValid ⟨256 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock5 : ∀ i : Fin 64, RootValid ⟨320 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock6 : ∀ i : Fin 64, RootValid ⟨384 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock7 : ∀ i : Fin 64, RootValid ⟨448 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock8 : ∀ i : Fin 64, RootValid ⟨512 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock9 : ∀ i : Fin 64, RootValid ⟨576 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock10 : ∀ i : Fin 64, RootValid ⟨640 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock11 : ∀ i : Fin 64, RootValid ⟨704 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock12 : ∀ i : Fin 64, RootValid ⟨768 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock13 : ∀ i : Fin 64, RootValid ⟨832 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock14 : ∀ i : Fin 64, RootValid ⟨896 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock15 : ∀ i : Fin 64, RootValid ⟨960 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock16 : ∀ i : Fin 64, RootValid ⟨1024 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock17 : ∀ i : Fin 64, RootValid ⟨1088 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock18 : ∀ i : Fin 64, RootValid ⟨1152 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock19 : ∀ i : Fin 64, RootValid ⟨1216 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock20 : ∀ i : Fin 64, RootValid ⟨1280 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock21 : ∀ i : Fin 64, RootValid ⟨1344 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock22 : ∀ i : Fin 64, RootValid ⟨1408 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock23 : ∀ i : Fin 64, RootValid ⟨1472 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock24 : ∀ i : Fin 64, RootValid ⟨1536 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock25 : ∀ i : Fin 64, RootValid ⟨1600 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock26 : ∀ i : Fin 64, RootValid ⟨1664 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock27 : ∀ i : Fin 64, RootValid ⟨1728 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock28 : ∀ i : Fin 64, RootValid ⟨1792 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock29 : ∀ i : Fin 64, RootValid ⟨1856 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock30 : ∀ i : Fin 64, RootValid ⟨1920 + i.val, by omega⟩ := by
  decide +kernel

private theorem rootBlock31 : ∀ i : Fin 64, RootValid ⟨1984 + i.val, by omega⟩ := by
  decide +kernel

theorem root_valid (m : Fin 2048) : RootValid m := by
  have h : ∀ b : Fin 32, ∀ i : Fin 64, RootValid ⟨64 * b.val + i.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact rootBlock0
    · exact rootBlock1
    · exact rootBlock2
    · exact rootBlock3
    · exact rootBlock4
    · exact rootBlock5
    · exact rootBlock6
    · exact rootBlock7
    · exact rootBlock8
    · exact rootBlock9
    · exact rootBlock10
    · exact rootBlock11
    · exact rootBlock12
    · exact rootBlock13
    · exact rootBlock14
    · exact rootBlock15
    · exact rootBlock16
    · exact rootBlock17
    · exact rootBlock18
    · exact rootBlock19
    · exact rootBlock20
    · exact rootBlock21
    · exact rootBlock22
    · exact rootBlock23
    · exact rootBlock24
    · exact rootBlock25
    · exact rootBlock26
    · exact rootBlock27
    · exact rootBlock28
    · exact rootBlock29
    · exact rootBlock30
    · exact rootBlock31
  convert h ⟨m.val / 64, by omega⟩ ⟨m.val % 64, Nat.mod_lt _ (by decide)⟩ using 1
  apply Fin.ext
  exact (Nat.div_add_mod m.val 64).symm

def bridge1 (_m : ℕ) : ℕ × ℕ :=
  (19, 990)

def bridge2 (m : ℕ) : ℕ × ℕ :=
  if m < 841 then
    if m < 350 then
      if m < 151 then
        if m < 91 then
          if m < 47 then
            (610, 2039)
          else
            (226, 2017)
        else
          (226, 2017)
      else
        if m < 227 then
          (226, 2017)
        else
          if m < 261 then
            (610, 2039)
          else
            if m < 298 then
              (226, 2017)
            else
              (610, 2039)
    else
      if m < 569 then
        if m < 456 then
          (226, 2017)
        else
          if m < 534 then
            (610, 2039)
          else
            (226, 2017)
      else
        (226, 2017)
  else
    if m < 1527 then
      (226, 2017)
    else
      if m < 1795 then
        if m < 1738 then
          if m < 1576 then
            (226, 2017)
          else
            (610, 2039)
        else
          if m < 1764 then
            (610, 2039)
          else
            (226, 2017)
      else
        if m < 1978 then
          if m < 1881 then
            (610, 2039)
          else
            (226, 2017)
        else
          if m < 1998 then
            (226, 2017)
          else
            if m < 2017 then
              (226, 2017)
            else
              (610, 2039)

def bridge3 (m : ℕ) : ℕ × ℕ :=
  if m < 841 then
    if m < 350 then
      if m < 151 then
        if m < 91 then
          if m < 47 then
            (204, 2017)
          else
            (205, 2045)
        else
          (205, 2045)
      else
        if m < 227 then
          (205, 2045)
        else
          if m < 261 then
            (205, 2045)
          else
            (204, 2017)
    else
      if m < 569 then
        (204, 2017)
      else
        if m < 640 then
          (204, 2017)
        else
          if m < 686 then
            (204, 2017)
          else
            if m < 787 then
              (204, 2017)
            else
              (205, 2045)
  else
    if m < 1527 then
      if m < 1099 then
        if m < 1041 then
          if m < 991 then
            (204, 2017)
          else
            (205, 2045)
        else
          (204, 2017)
      else
        if m < 1158 then
          (204, 2017)
        else
          if m < 1339 then
            (204, 2017)
          else
            if m < 1410 then
              (205, 2045)
            else
              (204, 2017)
    else
      if m < 1795 then
        if m < 1738 then
          (205, 2045)
        else
          if m < 1764 then
            (204, 2017)
          else
            (205, 2045)
      else
        (204, 2017)

def bridge4 (m : ℕ) : ℕ × ℕ :=
  if m < 841 then
    if m < 350 then
      if m < 151 then
        if m < 91 then
          if m < 47 then
            (368, 2043)
          else
            (185, 2045)
        else
          (185, 2045)
      else
        if m < 227 then
          if m < 184 then
            (185, 2045)
          else
            (369, 2023)
        else
          (185, 2045)
    else
      if m < 569 then
        (185, 2045)
      else
        if m < 640 then
          if m < 589 then
            (369, 2023)
          else
            (185, 2045)
        else
          if m < 686 then
            (368, 2043)
          else
            (185, 2045)
  else
    if m < 1527 then
      if m < 1099 then
        (185, 2045)
      else
        if m < 1158 then
          (185, 2045)
        else
          if m < 1339 then
            (185, 2045)
          else
            if m < 1410 then
              (369, 2023)
            else
              (368, 2043)
    else
      if m < 1795 then
        (185, 2045)
      else
        if m < 1978 then
          if m < 1881 then
            (368, 2043)
          else
            (185, 2045)
        else
          if m < 1998 then
            (369, 2023)
          else
            (185, 2045)

def bridge5 (m : ℕ) : ℕ × ℕ :=
  if m < 841 then
    if m < 350 then
      if m < 151 then
        if m < 91 then
          if m < 47 then
            (1244, 2035)
          else
            (150, 2017)
        else
          (150, 2017)
      else
        if m < 227 then
          if m < 184 then
            (1245, 2031)
          else
            (150, 2017)
        else
          (150, 2017)
    else
      if m < 569 then
        if m < 456 then
          if m < 445 then
            (1245, 2031)
          else
            (150, 2017)
        else
          if m < 534 then
            (1244, 2035)
          else
            (1245, 2031)
      else
        if m < 640 then
          (150, 2017)
        else
          if m < 686 then
            (1244, 2035)
          else
            (150, 2017)
  else
    if m < 1527 then
      if m < 1099 then
        if m < 1041 then
          if m < 991 then
            (1244, 2035)
          else
            (1245, 2031)
        else
          (150, 2017)
      else
        (150, 2017)
    else
      (150, 2017)

def bridge6 (m : ℕ) : ℕ × ℕ :=
  if m < 841 then
    if m < 350 then
      if m < 151 then
        if m < 91 then
          if m < 47 then
            (756, 2039)
          else
            (117, 2045)
        else
          if m < 116 then
            (117, 2045)
          else
            (757, 2027)
      else
        (117, 2045)
    else
      if m < 569 then
        if m < 456 then
          if m < 445 then
            (117, 2045)
          else
            (757, 2027)
        else
          if m < 534 then
            (756, 2039)
          else
            (117, 2045)
      else
        (117, 2045)
  else
    if m < 1527 then
      if m < 1099 then
        if m < 1041 then
          (117, 2045)
        else
          if m < 1086 then
            (117, 2045)
          else
            (757, 2027)
      else
        if m < 1158 then
          if m < 1125 then
            (756, 2039)
          else
            (117, 2045)
        else
          if m < 1339 then
            (117, 2045)
          else
            if m < 1410 then
              (117, 2045)
            else
              (756, 2039)
    else
      if m < 1795 then
        if m < 1738 then
          if m < 1576 then
            (757, 2027)
          else
            (117, 2045)
        else
          (117, 2045)
      else
        (117, 2045)

def bridge7 (m : ℕ) : ℕ × ℕ :=
  if m < 841 then
    if m < 350 then
      if m < 151 then
        if m < 91 then
          if m < 47 then
            (402, 2043)
          else
            (90, 2017)
        else
          if m < 116 then
            (402, 2043)
          else
            (90, 2017)
      else
        (90, 2017)
    else
      if m < 569 then
        (90, 2017)
      else
        if m < 640 then
          (90, 2017)
        else
          if m < 686 then
            (90, 2017)
          else
            if m < 787 then
              (90, 2017)
            else
              (402, 2043)
  else
    if m < 1527 then
      if m < 1099 then
        if m < 1041 then
          if m < 991 then
            (402, 2043)
          else
            (90, 2017)
        else
          if m < 1086 then
            (402, 2043)
          else
            (90, 2017)
      else
        if m < 1158 then
          if m < 1125 then
            (402, 2043)
          else
            (90, 2017)
        else
          (90, 2017)
    else
      if m < 1795 then
        (90, 2017)
      else
        if m < 1978 then
          (402, 2043)
        else
          (90, 2017)

def bridge8 (m : ℕ) : ℕ × ℕ :=
  if m < 841 then
    if m < 350 then
      if m < 151 then
        if m < 91 then
          (486, 2043)
        else
          (46, 2017)
      else
        (46, 2017)
    else
      if m < 569 then
        (46, 2017)
      else
        if m < 640 then
          (46, 2017)
        else
          if m < 686 then
            (486, 2043)
          else
            if m < 787 then
              (486, 2043)
            else
              (46, 2017)
  else
    if m < 1527 then
      if m < 1099 then
        (46, 2017)
      else
        if m < 1158 then
          (486, 2043)
        else
          (46, 2017)
    else
      if m < 1795 then
        if m < 1738 then
          (46, 2017)
        else
          (486, 2043)
      else
        (46, 2017)

def bridge (i : Fin 10) (m : ℕ) : ℕ × ℕ :=
  ![(0,0), bridge1 m, bridge2 m, bridge3 m, bridge4 m, bridge5 m, bridge6 m, bridge7 m, bridge8 m, (0,0)] i

def action (i : Fin 10) (m : ℕ) : ℕ :=
  maskImage (InvolutionFibers.actionMasks (decide (2 ≤ i.val))) m

private theorem actionMasks_bound : ∀ b (m : Fin 2048),
    maskImage (InvolutionFibers.actionMasks b) m.val < 2048 := by decide +kernel

theorem action_bound (i : Fin 10) (m : Fin 2048) : action i m.val < 2048 :=
  actionMasks_bound _ m

def target (i : Fin 10) : Fin 10 := if i.val < 2 then 0 else 9

def BridgeValid (i : Fin 10) (m : Fin 2048) : Prop :=
  orbitRoot m.val = 1 → i ≠ 0 → i ≠ 9 → action i m.val = m.val →
    let n := (bridge i m.val).1
    let k := (bridge i m.val).2
    n < 2048 ∧ k < 2048 ∧ Nat.xor m.val n < 2048 ∧
    orbitRoot n = 3 ∧ orbitRoot (Nat.xor m.val n) = 3 ∧
    action i n = n ∧
    Nat.xor (Nat.xor (action i k) (Nat.xor (outsideMask i) n)) k = outsideMask (target i)

instance (i : Fin 10) (m : Fin 2048) : Decidable (BridgeValid i m) :=
  inferInstanceAs (Decidable (_ → _ → _ → _ → _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem bridgeCase0 : ∀ m : Fin 2048, BridgeValid 0 m := by
  decide +kernel

private theorem bridgeCase1 : ∀ m : Fin 2048, BridgeValid 1 m := by
  decide +kernel

private theorem bridgeCase2 : ∀ m : Fin 2048, BridgeValid 2 m := by
  decide +kernel

private theorem bridgeCase3 : ∀ m : Fin 2048, BridgeValid 3 m := by
  decide +kernel

private theorem bridgeCase4 : ∀ m : Fin 2048, BridgeValid 4 m := by
  decide +kernel

private theorem bridgeCase5 : ∀ m : Fin 2048, BridgeValid 5 m := by
  decide +kernel

private theorem bridgeCase6 : ∀ m : Fin 2048, BridgeValid 6 m := by
  decide +kernel

private theorem bridgeCase7 : ∀ m : Fin 2048, BridgeValid 7 m := by
  decide +kernel

private theorem bridgeCase8 : ∀ m : Fin 2048, BridgeValid 8 m := by
  decide +kernel

private theorem bridgeCase9 : ∀ m : Fin 2048, BridgeValid 9 m := by
  decide +kernel

theorem bridge_valid (i : Fin 10) (m : Fin 2048) : BridgeValid i m := by
  fin_cases i
  · exact bridgeCase0 m
  · exact bridgeCase1 m
  · exact bridgeCase2 m
  · exact bridgeCase3 m
  · exact bridgeCase4 m
  · exact bridgeCase5 m
  · exact bridgeCase6 m
  · exact bridgeCase7 m
  · exact bridgeCase8 m
  · exact bridgeCase9 m

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf.PureSecondData
