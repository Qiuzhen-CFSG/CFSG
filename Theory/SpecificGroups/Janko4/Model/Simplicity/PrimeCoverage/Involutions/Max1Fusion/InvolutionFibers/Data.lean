module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideSetup
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData

/-!
# Finite affine involution-fiber certificates

The two right actions are those of x and q=(xy)^7 on the certified binary
kernel. Their square masks are 0 and 1. For each solution of the affine
square-one equation, the tables give a kernel conjugator and an index in the
ten concrete representatives. Every mask is checked by kernel reduction.
The generating search in `source/generate.py` is not trusted.
Source words: ATLAS J4G1-max1W1, documented in Cardinality.Subgroup.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Janko4.Simplicity.Max1Fusion.InvolutionFibers
open Cardinality.KernelCount Cardinality.QuotientCount.Image

def qMasks : Fin 11 → ℕ := ![1, 1793, 1742, 1418, 857, 1131, 392, 512, 1994, 128, 1865]

def xyAction (m : ℕ) : ℕ := maskImage yMasks (maskImage xMasks m)

theorem qMasks_basis : ∀ i : Fin 11,
    (xyAction^[7]) (2 ^ i.val) = qMasks i := by decide +kernel

def actionMasks (b : Bool) : Fin 11 → ℕ := if b then qMasks else xMasks

def squareMask (b : Bool) : ℕ := if b then 1 else 0

def xWitness (m : ℕ) : Fin 10 × ℕ :=
  if m < 768 then
    if m < 160 then
      if m < 96 then
        if m < 16 then
          if m < 12 then
            if m < 3 then
              (0, 0)
            else
              (0, 1)
          else
            if m < 15 then
              (0, 4)
            else
              (0, 5)
        else
          if m < 28 then
            if m < 19 then
              (1, 0)
            else
              (1, 1)
          else
            if m < 31 then
              (1, 4)
            else
              (1, 5)
      else
        if m < 112 then
          if m < 108 then
            if m < 99 then
              (0, 32)
            else
              (0, 33)
          else
            if m < 111 then
              (0, 36)
            else
              (0, 37)
        else
          if m < 124 then
            if m < 115 then
              (1, 32)
            else
              (1, 33)
          else
            if m < 127 then
              (1, 36)
            else
              (1, 37)
    else
      if m < 192 then
        if m < 176 then
          if m < 172 then
            if m < 163 then
              (0, 1280)
            else
              (0, 1281)
          else
            if m < 175 then
              (0, 1284)
            else
              (0, 1285)
        else
          if m < 188 then
            if m < 179 then
              (1, 1280)
            else
              (1, 1281)
          else
            if m < 191 then
              (1, 1284)
            else
              (1, 1285)
      else
        if m < 208 then
          if m < 204 then
            if m < 195 then
              (0, 1312)
            else
              (0, 1313)
          else
            if m < 207 then
              (0, 1316)
            else
              (0, 1317)
        else
          if m < 220 then
            if m < 211 then
              (1, 1312)
            else
              (1, 1313)
          else
            if m < 223 then
              (1, 1316)
            else
              (1, 1317)
  else
    if m < 928 then
      if m < 864 then
        if m < 784 then
          if m < 780 then
            if m < 771 then
              (0, 256)
            else
              (0, 257)
          else
            if m < 783 then
              (0, 260)
            else
              (0, 261)
        else
          if m < 796 then
            if m < 787 then
              (1, 256)
            else
              (1, 257)
          else
            if m < 799 then
              (1, 260)
            else
              (1, 261)
      else
        if m < 880 then
          if m < 876 then
            if m < 867 then
              (0, 288)
            else
              (0, 289)
          else
            if m < 879 then
              (0, 292)
            else
              (0, 293)
        else
          if m < 892 then
            if m < 883 then
              (1, 288)
            else
              (1, 289)
          else
            if m < 895 then
              (1, 292)
            else
              (1, 293)
    else
      if m < 960 then
        if m < 944 then
          if m < 940 then
            if m < 931 then
              (0, 1024)
            else
              (0, 1025)
          else
            if m < 943 then
              (0, 1028)
            else
              (0, 1029)
        else
          if m < 956 then
            if m < 947 then
              (1, 1024)
            else
              (1, 1025)
          else
            if m < 959 then
              (1, 1028)
            else
              (1, 1029)
      else
        if m < 976 then
          if m < 972 then
            if m < 963 then
              (0, 1056)
            else
              (0, 1057)
          else
            if m < 975 then
              (0, 1060)
            else
              (0, 1061)
        else
          if m < 988 then
            if m < 979 then
              (1, 1056)
            else
              (1, 1057)
          else
            if m < 991 then
              (1, 1060)
            else
              (1, 1061)

def qWitness (m : ℕ) : Fin 10 × ℕ :=
  if m < 1036 then
    if m < 522 then
      if m < 280 then
        if m < 138 then
          if m < 70 then
            if m < 50 then
              if m < 29 then
                (2, 0)
              else
                (2, 28)
            else
              if m < 51 then
                (3, 0)
              else
                (3, 28)
          else
            if m < 104 then
              if m < 71 then
                (4, 0)
              else
                (4, 28)
            else
              if m < 105 then
                (5, 0)
              else
                (5, 28)
        else
          if m < 208 then
            if m < 164 then
              if m < 139 then
                (6, 0)
              else
                (6, 28)
            else
              if m < 165 then
                (7, 0)
              else
                (7, 28)
          else
            if m < 254 then
              if m < 209 then
                (8, 0)
              else
                (8, 28)
            else
              if m < 255 then
                (9, 0)
              else
                (9, 28)
      else
        if m < 398 then
          if m < 322 then
            if m < 310 then
              if m < 281 then
                (8, 26)
              else
                (8, 6)
            else
              if m < 311 then
                (9, 26)
              else
                (9, 6)
          else
            if m < 364 then
              if m < 323 then
                (6, 26)
              else
                (6, 6)
            else
              if m < 365 then
                (7, 26)
              else
                (7, 6)
        else
          if m < 468 then
            if m < 416 then
              if m < 399 then
                (4, 26)
              else
                (4, 6)
            else
              if m < 417 then
                (5, 26)
              else
                (5, 6)
          else
            if m < 506 then
              if m < 469 then
                (2, 26)
              else
                (2, 6)
            else
              if m < 507 then
                (3, 26)
              else
                (3, 6)
    else
      if m < 782 then
        if m < 668 then
          if m < 592 then
            if m < 548 then
              if m < 523 then
                (6, 22)
              else
                (6, 10)
            else
              if m < 549 then
                (7, 22)
              else
                (7, 10)
          else
            if m < 638 then
              if m < 593 then
                (8, 22)
              else
                (8, 10)
            else
              if m < 639 then
                (9, 22)
              else
                (9, 10)
        else
          if m < 710 then
            if m < 690 then
              if m < 669 then
                (2, 22)
              else
                (2, 10)
            else
              if m < 691 then
                (3, 22)
              else
                (3, 10)
          else
            if m < 744 then
              if m < 711 then
                (4, 22)
              else
                (4, 10)
            else
              if m < 745 then
                (5, 22)
              else
                (5, 10)
      else
        if m < 920 then
          if m < 852 then
            if m < 800 then
              if m < 783 then
                (4, 12)
              else
                (4, 16)
            else
              if m < 801 then
                (5, 12)
              else
                (5, 16)
          else
            if m < 890 then
              if m < 853 then
                (2, 12)
              else
                (2, 16)
            else
              if m < 891 then
                (3, 12)
              else
                (3, 16)
        else
          if m < 962 then
            if m < 950 then
              if m < 921 then
                (8, 12)
              else
                (8, 16)
            else
              if m < 951 then
                (9, 12)
              else
                (9, 16)
          else
            if m < 1004 then
              if m < 963 then
                (6, 12)
              else
                (6, 16)
            else
              if m < 1005 then
                (7, 12)
              else
                (7, 16)
  else
    if m < 1562 then
      if m < 1288 then
        if m < 1178 then
          if m < 1110 then
            if m < 1058 then
              if m < 1037 then
                (4, 18)
              else
                (4, 14)
            else
              if m < 1059 then
                (5, 18)
              else
                (5, 14)
          else
            if m < 1144 then
              if m < 1111 then
                (2, 18)
              else
                (2, 14)
            else
              if m < 1145 then
                (3, 18)
              else
                (3, 14)
        else
          if m < 1216 then
            if m < 1204 then
              if m < 1179 then
                (8, 18)
              else
                (8, 14)
            else
              if m < 1205 then
                (9, 18)
              else
                (9, 14)
          else
            if m < 1262 then
              if m < 1217 then
                (6, 18)
              else
                (6, 14)
            else
              if m < 1263 then
                (7, 18)
              else
                (7, 14)
      else
        if m < 1438 then
          if m < 1362 then
            if m < 1318 then
              if m < 1289 then
                (6, 8)
              else
                (6, 20)
            else
              if m < 1319 then
                (7, 8)
              else
                (7, 20)
          else
            if m < 1404 then
              if m < 1363 then
                (8, 8)
              else
                (8, 20)
            else
              if m < 1405 then
                (9, 8)
              else
                (9, 20)
        else
          if m < 1476 then
            if m < 1456 then
              if m < 1439 then
                (2, 8)
              else
                (2, 20)
            else
              if m < 1457 then
                (3, 8)
              else
                (3, 20)
          else
            if m < 1514 then
              if m < 1477 then
                (4, 8)
              else
                (4, 20)
            else
              if m < 1515 then
                (5, 8)
              else
                (5, 20)
    else
      if m < 1822 then
        if m < 1676 then
          if m < 1600 then
            if m < 1588 then
              if m < 1563 then
                (8, 4)
              else
                (8, 24)
            else
              if m < 1589 then
                (9, 4)
              else
                (9, 24)
          else
            if m < 1646 then
              if m < 1601 then
                (6, 4)
              else
                (6, 24)
            else
              if m < 1647 then
                (7, 4)
              else
                (7, 24)
        else
          if m < 1750 then
            if m < 1698 then
              if m < 1677 then
                (4, 4)
              else
                (4, 24)
            else
              if m < 1699 then
                (5, 4)
              else
                (5, 24)
          else
            if m < 1784 then
              if m < 1751 then
                (2, 4)
              else
                (2, 24)
            else
              if m < 1785 then
                (3, 4)
              else
                (3, 24)
      else
        if m < 1928 then
          if m < 1860 then
            if m < 1840 then
              if m < 1823 then
                (2, 30)
              else
                (2, 2)
            else
              if m < 1841 then
                (3, 30)
              else
                (3, 2)
          else
            if m < 1898 then
              if m < 1861 then
                (4, 30)
              else
                (4, 2)
            else
              if m < 1899 then
                (5, 30)
              else
                (5, 2)
        else
          if m < 2002 then
            if m < 1958 then
              if m < 1929 then
                (6, 30)
              else
                (6, 2)
            else
              if m < 1959 then
                (7, 30)
              else
                (7, 2)
          else
            if m < 2044 then
              if m < 2003 then
                (8, 30)
              else
                (8, 2)
            else
              if m < 2045 then
                (9, 30)
              else
                (9, 2)

def witness (b : Bool) (m : ℕ) : Fin 10 × ℕ :=
  if b then qWitness m else xWitness m

theorem square_bound : ∀ b (m : Fin 2048),
    Nat.xor (maskImage (actionMasks b) m.val) m.val < 2048 := by decide +kernel

/-- Each affine solution is reduced by an explicit element of the binary kernel. -/
theorem reduction : ∀ b (m : Fin 2048),
    Nat.xor (maskImage (actionMasks b) m.val) m.val = squareMask b →
    ((witness b m.val).1.val < 2 ↔ b = false) ∧
    Nat.xor (Nat.xor (maskImage (actionMasks b) (witness b m.val).2) m.val)
      (witness b m.val).2 = outsideMask (witness b m.val).1 := by decide +kernel

end Janko4.Simplicity.Max1Fusion.InvolutionFibers
