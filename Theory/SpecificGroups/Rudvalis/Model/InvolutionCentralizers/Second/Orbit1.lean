module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second.Orbit0

/-!
# Certified orbit representatives for point 1

Untrusted finite witnesses for the literal ATLAS generator a and its two-point
centralizer stabilizer chain. Every equation used below is checked by Lean's
kernel. No centralizer order or product structure is assumed.
Source: RuG1-p4060B0, attributed in Model.PermutationData; GLS3 Table 5.3r.
Reproduction data and procedure are in Second/source/.
-/

set_option Elab.async false
namespace Rudvalis.InvolutionCentralizers.SecondCertificate
open OuterNormalizer OuterNormalizer.InvarianceCertificate OuterNormalizer.RigidityCertificate

@[expose] public def h0 : Model := ([3, 3, 3, 6, 7, 7, 7].map letters0).prod

@[expose] public def h1 : Model := ([6, 7, 7, 2, 3, 3, 2].map letters0).prod

@[expose] public def h2 : Model := ([6, 3, 3, 6, 3, 2, 7, 2, 3, 3].map letters0).prod

@[expose] public def letters1 : Fin 6 → Model := ![h0, h1, h2, h0⁻¹, h1⁻¹, h2⁻¹]

public theorem letters1_mem (i : Fin 6) : letters1 i ∈ Subgroup.centralizer ({a} : Set Model) := by
  fin_cases i
  · exact word_centralizes letters0 letters0_mem _
  · exact word_centralizes letters0 letters0_mem _
  · exact word_centralizes letters0 letters0_mem _
  · apply (Subgroup.centralizer _).inv_mem
    exact word_centralizes letters0 letters0_mem _
  · apply (Subgroup.centralizer _).inv_mem
    exact word_centralizes letters0 letters0_mem _
  · apply (Subgroup.centralizer _).inv_mem
    exact word_centralizes letters0 letters0_mem _

@[expose] public def words1 : Array (List (Fin 6)) := #[
[],
[0],
[1],
[2],
[5],
[1, 0],
[2, 0],
[5, 0],
[0, 1],
[2, 1],
[5, 1],
[0, 2],
[1, 2],
[2, 2],
[0, 5],
[1, 5],
[0, 1, 0],
[0, 2, 0],
[1, 2, 0],
[2, 2, 0],
[0, 5, 0],
[1, 5, 0],
[5, 0, 1],
[0, 2, 1],
[1, 2, 1],
[0, 5, 1],
[1, 5, 1],
[1, 0, 2],
[2, 0, 2],
[2, 1, 2],
[5, 1, 2],
[0, 2, 2],
[2, 0, 5],
[5, 0, 5],
[2, 1, 5],
[5, 1, 5],
[5, 0, 1, 0],
[1, 0, 2, 0],
[2, 0, 2, 0],
[2, 1, 2, 0],
[5, 1, 2, 0],
[0, 2, 2, 0],
[0, 5, 0, 1],
[1, 5, 0, 1],
[1, 0, 2, 1],
[2, 0, 2, 1],
[2, 1, 2, 1],
[5, 1, 2, 1],
[2, 0, 5, 1],
[2, 1, 5, 1],
[5, 1, 5, 1],
[0, 1, 0, 2]]

@[expose] public def rep1 (i : Fin 52) : Model := (words1[i.val]!.map letters1).prod

public theorem rep1_mem (i : Fin 52) : rep1 i ∈ Subgroup.centralizer ({a} : Set Model) :=
  word_centralizes letters1 letters1_mem _

@[expose] public def point1Data : Array Nat := #[
7403566346134079665913786266344437294253924351496399344846987087363683598012656439856405714029680225091692195991187277033394639119260444900132382265281023268216757651573827356323661864961]

@[expose] public def point1 (x : Fin 52) : Fin 4060 :=
  ⟨((point1Data[x.val / 64]! >>> (12 * (x.val % 64))) % 4096) % 4060, Nat.mod_lt _ (by decide)⟩

@[expose] public def pointInv1Data : Array Nat := #[
0,
241892432155202854740203766301391982037137713701342149769198822904089522087457382101134769273333568503808,
0,
124615124605053091942943915581112320,
0,
0,
6648885426755762585580206726968210317671992836925615922076362426692700562427531008982609035264,
1511157274518286468382720,
3079649020494480789516483135781610882417262558697643111126891980157483849586833414212080374347930271744,
0,
1017690184272826215191977319181844480,
4503599627370496,
4212491666742287467916721107346817292755803816021964450172439101440,
25833968410512165506784286602625459102416278954387258945427054332213807851497792902550150109945430053765513216,
152302642468157908505125113119501069619989403291270866830190234761808839875079638868791859653773335986176,
1532495593674053488478862626306890053250059168345227264,
8462480737302404222943232,
0,
0,
0,
0,
0,
444641622671294190426512582433361566156556741116059765911517122590386417817354240,
0,
334243113205869977312728115206961821324618222706820909742686208,
16627864965928018459178451490940130320775096171470038147097519085555190851641514858507634510048411227521024,
0,
0,
0,
233120267067087488510335428818822268797088820686256742550217489168668514224625019781120,
19085346751378575868447660048507062938225003779979495074870306437785776377308201205891471985683372021610667988484096,
0,
0,
3802951800684688204490109616128,
0,
0,
4820814970860469737702412686247083203426986801599000273223680,
341757925747345613183203472987128338336432723577064443191526657251555156124902488003673933909852160,
14073748835532800,
4735255424800214610366188397882327334940866670189590083051292748738579195187695714304,
179449926349046518120448,
1298074214633706907132624082305024,
0,
0,
1435383288138851575369454586545939021013017439023670661404411984382635579853076161883957607467581440,
0,
3486039150627630854115933814784,
0,
0,
0,
0,
883423532389192164791648750371459257913741948437809479060803100646309888,
0,
0,
1918220898996810080142336342940121463298411462656,
1231371407201896821214417240144407664834426244265767916370151851156967110584915696817782683739496826669718057254912,
3927785650326801592672402987925010615325318709248,
12281925456545232973771374810474924658965551003550753427195489244977763423238683169950381394362368,
16909007112171056410979908815075074004499649538888681249670786216624930369264578954526720,
0,
0,
140304157183766680147553743940763169886969524125696,
5088519546561746869199896802139605325583153623001782599390225859722744954899,
3467987885857395703808]

@[expose] public def pointInv1 (x : Fin 4060) : Fin 52 :=
  ⟨((pointInv1Data[x.val / 64]! >>> (6 * (x.val % 64))) % 64) % 52, Nat.mod_lt _ (by decide)⟩

private def orbit1Facts (x : Fin 4060) : Prop :=
  if h : x.val < 52 then (rep1 ⟨x.val,h⟩).val 1 = point1 ⟨x.val,h⟩ ∧ pointInv1 (point1 ⟨x.val,h⟩) = ⟨x.val,h⟩ ∧ (rep1 ⟨x.val,h⟩).val 0 = 0 else True

private instance (x : Fin 4060) : Decidable (orbit1Facts x) := inferInstanceAs (Decidable (if h : x.val < 52 then (rep1 ⟨x.val,h⟩).val 1 = point1 ⟨x.val,h⟩ ∧ pointInv1 (point1 ⟨x.val,h⟩) = ⟨x.val,h⟩ ∧ (rep1 ⟨x.val,h⟩).val 0 = 0 else True))

private theorem orbit1Facts_b0 : checkBlock orbit1Facts 0 = true := by decide +kernel

private theorem orbit1Facts_b1 : checkBlock orbit1Facts 1 = true := by decide +kernel

private theorem orbit1Facts_b2 : checkBlock orbit1Facts 2 = true := by decide +kernel

private theorem orbit1Facts_b3 : checkBlock orbit1Facts 3 = true := by decide +kernel

private theorem orbit1Facts_b4 : checkBlock orbit1Facts 4 = true := by decide +kernel

private theorem orbit1Facts_b5 : checkBlock orbit1Facts 5 = true := by decide +kernel

private theorem orbit1Facts_b6 : checkBlock orbit1Facts 6 = true := by decide +kernel

private theorem orbit1Facts_b7 : checkBlock orbit1Facts 7 = true := by decide +kernel

private theorem orbit1Facts_b8 : checkBlock orbit1Facts 8 = true := by decide +kernel

private theorem orbit1Facts_b9 : checkBlock orbit1Facts 9 = true := by decide +kernel

private theorem orbit1Facts_b10 : checkBlock orbit1Facts 10 = true := by decide +kernel

private theorem orbit1Facts_b11 : checkBlock orbit1Facts 11 = true := by decide +kernel

private theorem orbit1Facts_b12 : checkBlock orbit1Facts 12 = true := by decide +kernel

private theorem orbit1Facts_b13 : checkBlock orbit1Facts 13 = true := by decide +kernel

private theorem orbit1Facts_b14 : checkBlock orbit1Facts 14 = true := by decide +kernel

private theorem orbit1Facts_b15 : checkBlock orbit1Facts 15 = true := by decide +kernel

private theorem orbit1Facts_b16 : checkBlock orbit1Facts 16 = true := by decide +kernel

private theorem orbit1Facts_b17 : checkBlock orbit1Facts 17 = true := by decide +kernel

private theorem orbit1Facts_b18 : checkBlock orbit1Facts 18 = true := by decide +kernel

private theorem orbit1Facts_b19 : checkBlock orbit1Facts 19 = true := by decide +kernel

private theorem orbit1Facts_b20 : checkBlock orbit1Facts 20 = true := by decide +kernel

private theorem orbit1Facts_b21 : checkBlock orbit1Facts 21 = true := by decide +kernel

private theorem orbit1Facts_b22 : checkBlock orbit1Facts 22 = true := by decide +kernel

private theorem orbit1Facts_b23 : checkBlock orbit1Facts 23 = true := by decide +kernel

private theorem orbit1Facts_b24 : checkBlock orbit1Facts 24 = true := by decide +kernel

private theorem orbit1Facts_b25 : checkBlock orbit1Facts 25 = true := by decide +kernel

private theorem orbit1Facts_b26 : checkBlock orbit1Facts 26 = true := by decide +kernel

private theorem orbit1Facts_b27 : checkBlock orbit1Facts 27 = true := by decide +kernel

private theorem orbit1Facts_b28 : checkBlock orbit1Facts 28 = true := by decide +kernel

private theorem orbit1Facts_b29 : checkBlock orbit1Facts 29 = true := by decide +kernel

private theorem orbit1Facts_b30 : checkBlock orbit1Facts 30 = true := by decide +kernel

private theorem orbit1Facts_b31 : checkBlock orbit1Facts 31 = true := by decide +kernel

private theorem orbit1Facts_b32 : checkBlock orbit1Facts 32 = true := by decide +kernel

private theorem orbit1Facts_b33 : checkBlock orbit1Facts 33 = true := by decide +kernel

private theorem orbit1Facts_b34 : checkBlock orbit1Facts 34 = true := by decide +kernel

private theorem orbit1Facts_b35 : checkBlock orbit1Facts 35 = true := by decide +kernel

private theorem orbit1Facts_b36 : checkBlock orbit1Facts 36 = true := by decide +kernel

private theorem orbit1Facts_b37 : checkBlock orbit1Facts 37 = true := by decide +kernel

private theorem orbit1Facts_b38 : checkBlock orbit1Facts 38 = true := by decide +kernel

private theorem orbit1Facts_b39 : checkBlock orbit1Facts 39 = true := by decide +kernel

private theorem orbit1Facts_b40 : checkBlock orbit1Facts 40 = true := by decide +kernel

private theorem orbit1Facts_b41 : checkBlock orbit1Facts 41 = true := by decide +kernel

private theorem orbit1Facts_b42 : checkBlock orbit1Facts 42 = true := by decide +kernel

private theorem orbit1Facts_b43 : checkBlock orbit1Facts 43 = true := by decide +kernel

private theorem orbit1Facts_b44 : checkBlock orbit1Facts 44 = true := by decide +kernel

private theorem orbit1Facts_b45 : checkBlock orbit1Facts 45 = true := by decide +kernel

private theorem orbit1Facts_b46 : checkBlock orbit1Facts 46 = true := by decide +kernel

private theorem orbit1Facts_b47 : checkBlock orbit1Facts 47 = true := by decide +kernel

private theorem orbit1Facts_b48 : checkBlock orbit1Facts 48 = true := by decide +kernel

private theorem orbit1Facts_b49 : checkBlock orbit1Facts 49 = true := by decide +kernel

private theorem orbit1Facts_b50 : checkBlock orbit1Facts 50 = true := by decide +kernel

private theorem orbit1Facts_b51 : checkBlock orbit1Facts 51 = true := by decide +kernel

private theorem orbit1Facts_b52 : checkBlock orbit1Facts 52 = true := by decide +kernel

private theorem orbit1Facts_b53 : checkBlock orbit1Facts 53 = true := by decide +kernel

private theorem orbit1Facts_b54 : checkBlock orbit1Facts 54 = true := by decide +kernel

private theorem orbit1Facts_b55 : checkBlock orbit1Facts 55 = true := by decide +kernel

private theorem orbit1Facts_b56 : checkBlock orbit1Facts 56 = true := by decide +kernel

private theorem orbit1Facts_b57 : checkBlock orbit1Facts 57 = true := by decide +kernel

private theorem orbit1Facts_b58 : checkBlock orbit1Facts 58 = true := by decide +kernel

private theorem orbit1Facts_b59 : checkBlock orbit1Facts 59 = true := by decide +kernel

private theorem orbit1Facts_b60 : checkBlock orbit1Facts 60 = true := by decide +kernel

private theorem orbit1Facts_b61 : checkBlock orbit1Facts 61 = true := by decide +kernel

private theorem orbit1Facts_b62 : checkBlock orbit1Facts 62 = true := by decide +kernel

private theorem orbit1Facts_b63 : checkBlock orbit1Facts 63 = true := by decide +kernel

private theorem orbit1Facts_all : ∀ x, orbit1Facts x := by
  apply allFinBlocks
  intro b
  fin_cases b
  · exact orbit1Facts_b0
  · exact orbit1Facts_b1
  · exact orbit1Facts_b2
  · exact orbit1Facts_b3
  · exact orbit1Facts_b4
  · exact orbit1Facts_b5
  · exact orbit1Facts_b6
  · exact orbit1Facts_b7
  · exact orbit1Facts_b8
  · exact orbit1Facts_b9
  · exact orbit1Facts_b10
  · exact orbit1Facts_b11
  · exact orbit1Facts_b12
  · exact orbit1Facts_b13
  · exact orbit1Facts_b14
  · exact orbit1Facts_b15
  · exact orbit1Facts_b16
  · exact orbit1Facts_b17
  · exact orbit1Facts_b18
  · exact orbit1Facts_b19
  · exact orbit1Facts_b20
  · exact orbit1Facts_b21
  · exact orbit1Facts_b22
  · exact orbit1Facts_b23
  · exact orbit1Facts_b24
  · exact orbit1Facts_b25
  · exact orbit1Facts_b26
  · exact orbit1Facts_b27
  · exact orbit1Facts_b28
  · exact orbit1Facts_b29
  · exact orbit1Facts_b30
  · exact orbit1Facts_b31
  · exact orbit1Facts_b32
  · exact orbit1Facts_b33
  · exact orbit1Facts_b34
  · exact orbit1Facts_b35
  · exact orbit1Facts_b36
  · exact orbit1Facts_b37
  · exact orbit1Facts_b38
  · exact orbit1Facts_b39
  · exact orbit1Facts_b40
  · exact orbit1Facts_b41
  · exact orbit1Facts_b42
  · exact orbit1Facts_b43
  · exact orbit1Facts_b44
  · exact orbit1Facts_b45
  · exact orbit1Facts_b46
  · exact orbit1Facts_b47
  · exact orbit1Facts_b48
  · exact orbit1Facts_b49
  · exact orbit1Facts_b50
  · exact orbit1Facts_b51
  · exact orbit1Facts_b52
  · exact orbit1Facts_b53
  · exact orbit1Facts_b54
  · exact orbit1Facts_b55
  · exact orbit1Facts_b56
  · exact orbit1Facts_b57
  · exact orbit1Facts_b58
  · exact orbit1Facts_b59
  · exact orbit1Facts_b60
  · exact orbit1Facts_b61
  · exact orbit1Facts_b62
  · exact orbit1Facts_b63

public theorem rep1_point (i : Fin 52) : (rep1 i).val 1 = point1 i := by
  have h := orbit1Facts_all ⟨i.val,by omega⟩
  simp only [orbit1Facts,dif_pos i.isLt] at h
  exact h.1

public theorem point1_left (i : Fin 52) : pointInv1 (point1 i) = i := by
  have h := orbit1Facts_all ⟨i.val,by omega⟩
  simp only [orbit1Facts,dif_pos i.isLt] at h
  exact h.2.1

public theorem rep1_fix (i : Fin 52) : (rep1 i).val 0 = 0 := by
  have h := orbit1Facts_all ⟨i.val,by omega⟩
  simp only [orbit1Facts,dif_pos i.isLt] at h
  exact h.2.2

end Rudvalis.InvolutionCentralizers.SecondCertificate
