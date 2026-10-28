module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleAmalgam
public import CFSG.Quasithin.ChapterB.Section02.BaumannCenter

/-!
# The nonsingular point amalgam in the paired outside case

Under the genuine A5 Context, outside omega movement, solvability and the
earlier Baumann normalizer bound, a center-free H has two original natural
S3 factors. Their fixed lines are the two nonsingular lines of V2. The
factor opposite the marked point centralizes it. Its quotient preimage,
adjoined to Baum(T), has index three over Baum(T) and S3 two-core quotient.
Sylow conjugacy of the factors and offender generation force this group
outside N_G(L).

On the other side, Baum(T) normalizes the literal O²(C_L(v)). The reverse
normalization would preserve Omega1 Z(Baum(T))=V2, although the singular
point's residual orbit spans an eight-element group. This contradiction
and index three give its S3 two-core quotient. The two local groups meet
in exactly Baum(T); their join is SQTK inside the involution centralizer.
This constructs the Goldschmidt triple in the opening of 13.2.12.

The final theorem applies to the actual contrary core-free Borel join.
The subsequent F.6.18 exclusions and nonblock arguments, independent
Baumann control, nonsolvable generation bound and single-factor endgame
remain with qt-d-1367-assembly. SourceAssembly/PairedPoint applies this
construction to the universal terminal consumer; no unconditional 13.2.7
or 13.2.12 is claimed here.

Source: Aschbacher--Smith 13.2.8, 13.2.11--12, printed pp.880--883.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The original Baumann subgroup is Sylow in the marked point centralizer. -/
theorem point_baumann_sylow
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (Gv (markedV d.flag.flag.module)) := by
  let v := markedV d.flag.flag.module
  let B := ChapterB.baumann (T : Subgroup G)
  have hBT : B = Tv (T : Subgroup G) v :=
    source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz v
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem
  have hMV : normalizer (L : Set G) ⊓ Gv v ≤ normalizer (V : Set G) :=
    inf_elementCentralizer_le_normalizer_of_trivial_intersections
      d.trivial_intersections (map_mem d.flag.flag.module _) (markedV_ne_one d.flag.flag.module)
  have he : normalizer (L : Set G) ⊓ Gv v = normalizer (V : Set G) ⊓ Gv v :=
    le_antisymm (le_inf hMV inf_le_right) (inf_le_inf_right _ d.module_normalizer)
  have hn : normalizer (B : Set G) ≤ normalizer (L : Set G) := hB
  have hi : ¬ 2 ∣ B.relIndex (Gv v) := by
    apply not_dvd_relIndex_of_normalizer_inf_le B (normalizer (L : Set G) ⊓ Gv v)
      (Gv v) (T.isPGroup'.to_le inf_le_left) (hBT ▸ inf_le_right)
    · rw [hBT,he]
      exact d.flag.flag_localIndex
    · exact inf_le_inf_right _ hn
  exact ⟨((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    : IsPGroup 2 (B.subgroupOf (Gv v))).toSylow hi,
    map_subgroupOf_eq_of_le (hBT ▸ inf_le_right)⟩

/-- The original Baumann subgroup normalizes the literal point residual. -/
theorem point_residual_normalized_by_baumann
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ChapterB.baumann (T : Subgroup G) ≤
      normalizer (Lv L (markedV d.flag.flag.module) : Set G) := by
  let v := markedV d.flag.flag.module
  have hc : ChapterB.baumann (T : Subgroup G) ≤ Gv v :=
    (source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz v
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right
  have hn : ChapterB.baumann (T : Subgroup G) ≤ normalizer (L ⊓ Gv v : Set G) :=
    le_normalizer_inf (inf_le_left.trans d.normalizes_L) (hc.trans (Gv v).le_normalizer)
  exact hn.trans (normalizer_le_normalizer_characteristic_image (L ⊓ Gv v)
    (pResidual 2 (L ⊓ Gv v : Subgroup G)))

/-- Reverse normalization contradicts the eight-element singular orbit span. -/
theorem point_residual_not_normalizes_baumann
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ¬ Lv L (markedV d.flag.flag.module) ≤
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  intro hn
  have hE : omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) = V₂ :=
    (ChapterB.omegaCenter_baumann_eq_thompsonAlpha _).trans
      (source_alpha_eq_flag_plane d hH hB hZ hs hz)
  have hnorm : Lv L (markedV d.flag.flag.module) ≤ normalizer (V₂ : Set G) := by
    suffices hh : Lv L (markedV d.flag.flag.module) ≤
        normalizer (omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) : Set G) by
      simpa only [hE] using hh
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (hn hg)]
  have hspan : Vv L (markedZ d.flag.flag.module) (markedV d.flag.flag.module) ≤ V₂ :=
    conjugateSpanBy_le (d.flag.flag.line_eq.le.trans d.flag.one_le_two) hnorm
  have hc := card_le_of_le hspan
  rw [Vv_card,d.flag.two_card] at hc
  omega

/-- The point residual adjoined to Baum(T) has the original local index three. -/
theorem point_residual_baumann_index
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    (ChapterB.baumann (T : Subgroup G)).relIndex
      (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) = 3 := by
  let C := Gv (markedV d.flag.flag.module)
  let A := Lv L (markedV d.flag.flag.module)
  let B := ChapterB.baumann (T : Subgroup G)
  have hAC : A ≤ C := (map_subtype_le _).trans inf_le_right
  obtain ⟨P,hP⟩ := point_baumann_sylow d hH hB hZ hs hz
  have hcard : Nat.card A = 3 * Nat.card (pCore 2 A) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),d.flag.flag.residualQuotient_card]
  have hAnot : ¬ IsPGroup 2 A := by
    intro hh
    have hq := hh.of_surjective (QuotientGroup.mk' (pCore 2 A))
      (QuotientGroup.mk'_surjective (pCore 2 A))
    rcases hq.card_eq_or_dvd with he | he <;>
      rw [d.flag.flag.residualQuotient_card] at he <;> norm_num at he
  have hindex := normalized_cubic_join_index_of_card_dvd P (A.subgroupOf C)
    (by
      intro p hp
      apply mem_normalizer_iff.mpr
      intro a
      exact mem_normalizer_iff.mp
        (point_residual_normalized_by_baumann d hH hB hZ hs hz
          (hP ▸ mem_map_of_mem C.subtype hp)) (a : G))
    (by
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
      exact ⟨n, by rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv,hcard,hn]⟩)
    (fun hh => hAnot (hh.of_equiv (subgroupOfEquivOfLe hAC)))
  have hm := relIndex_map_map_of_injective (P : Subgroup C)
    (A.subgroupOf C ⊔ (P : Subgroup C)) C.subtype_injective
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAC,hP] at hm
  exact hm.trans hindex

/-- The literal second point-local group has S3 two-core quotient. -/
theorem point_residual_baumann_core_quotient
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let J := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) := by
  let A := Lv L (markedV d.flag.flag.module)
  let B := ChapterB.baumann (T : Subgroup G)
  let J := A ⊔ B
  have hBJ : B ≤ J := le_sup_right
  have hJc : J ≤ Gv (markedV d.flag.flag.module) := sup_le
    ((map_subtype_le _).trans inf_le_right)
    ((source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right)
  have hi : (B.subgroupOf J).index = 3 := point_residual_baumann_index d hH hB hZ hs hz
  let P := ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    : IsPGroup 2 (B.subgroupOf J)).toSylow (show ¬ 2 ∣ (B.subgroupOf J).index by rw [hi]; decide)
  apply sylow_index_three_core_quotient P hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P)
  intro he
  change pCore 2 J = B.subgroupOf J at he
  have hn : (B.subgroupOf J).Normal := he ▸ inferInstance
  apply point_residual_not_normalizes_baumann d hH hB hZ hs hz
  exact (le_sup_left : A ≤ J).trans ((normal_subgroupOf_iff_le_normalizer hBJ).mp hn)


open Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise

omit d in
private theorem factor_preimage_card
    {Q W : Type*} [Group Q] [Finite Q] [AddCommGroup W] [Module (ZMod 2) W]
    (q : H →* Q) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    {ρ : Representation (ZMod 2) Q W} (c : ChapterB.SolvableFFFactors ρ)
    (i : Fin c.count) :
    (∃ n, Nat.card ((c.factor i).comap q) ∣ 3 * 2 ^ n) ∧
      ¬ IsPGroup 2 ((c.factor i).comap q) := by
  let A := (c.factor i).comap q
  let f : A →* c.factor i := (q.comp A.subtype).codRestrict _ (fun a => a.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    exact ⟨⟨x,by change q x ∈ c.factor i; rw [hx]; exact y.property⟩,Subtype.ext hx⟩
  have hfker : f.ker = q.ker.comap A.subtype := by ext x; exact Subtype.ext_iff
  have htwo : IsPGroup 2 f.ker := by
    rw [hfker]
    exact hk.comap_of_injective A.subtype A.subtype_injective
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  have hc : Nat.card A = 6 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,c.factor_card,hn]
  refine ⟨⟨n+1,?_⟩,?_⟩
  · rw [hc,pow_succ]
    rw [show 3 * (2 ^ n * 2) = 6 * 2 ^ n by ring]
  · intro hh
    have him := hh.of_surjective f hf
    rcases him.card_eq_or_dvd (p := 2) with he | he
    · rw [c.factor_card] at he
      norm_num at he
    · obtain ⟨k,hk⟩ := him.exists_card_eq
      have hd : 3 ∣ 2 ^ k := by rw [←hk,c.factor_card]; decide
      exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

omit d [Finite G] in
private theorem factor_preimage_not_le
    {Q W : Type*} [Group Q] [Finite Q] [AddCommGroup W] [Module (ZMod 2) W]
    (q : H →* Q) (hq : Function.Surjective q)
    (hTH : (T : Subgroup G) ≤ H)
    (hk : q.ker ≤ (T : Subgroup G).subgroupOf H)
    {ρ : Representation (ZMod 2) Q W} (c : ChapterB.SolvableFFFactors ρ)
    (ht : ∀ i j, ∃ t : T.subtype hTH,
      (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j)
    (hgen : offenderSubgroup ρ ⊔ ((T.subtype hTH : Sylow 2 H) : Subgroup H).map q = ⊤)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (hout : ¬H ≤ M)
    (i : Fin c.count) : ¬ ((c.factor i).comap q).map H.subtype ≤ M := by
  intro hi
  have hall (j : Fin c.count) : (c.factor j).comap q ≤ M.subgroupOf H := by
    obtain ⟨t,ht⟩ := ht i j
    intro x hx
    have hconj : q ((t : H)⁻¹ * x * t) ∈ c.factor i := by
      have hh : q x ∈ (c.factor i).map (MulAut.conj (q t)).toMonoidHom := ht.symm ▸ hx
      obtain ⟨y,hy,he⟩ := hh
      have heq : (q t)⁻¹ * q x * q t = y := by
        rw [←he]
        simp [MulAut.conj_apply,mul_assoc]
      rw [map_mul,map_mul,map_inv,heq]
      exact hy
    have hm := hi (mem_map_of_mem H.subtype hconj)
    have htM : ((t : H) : G) ∈ M := hTM t.property
    have hh := M.mul_mem (M.mul_mem htM hm) (M.inv_mem htM)
    change ((t : H) : G) * (((t : H) : G)⁻¹ * (x : G) * (t : H)) *
      ((t : H) : G)⁻¹ ∈ M at hh
    change (x : G) ∈ M
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_inv_cancel,mul_one] using hh
  have hMker : q.ker ≤ M.subgroupOf H := hk.trans (comap_mono hTM)
  have hO : offenderSubgroup ρ ≤ (M.subgroupOf H).map q := by
    rw [←c.iSup_factor]
    apply iSup_le
    intro j
    rw [←map_comap_eq_self_of_surjective hq (c.factor j)]
    exact map_mono (hall j)
  have htop : (M.subgroupOf H).map q = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le hO (map_mono (comap_mono hTM))
  have htopM : M.subgroupOf H = ⊤ := by
    rw [←comap_map_eq_self hMker,htop,comap_top]
  exact hout (fun x hx => show x ∈ M from htopM.ge (mem_top (⟨x,hx⟩ : H)))

/-- The first point-local group retains its actual natural-factor preimage
under H -> H/C_H(U_H), together with the opposite factor line containing v.
This is construction data for the later block exclusions. -/
@[expose] def IsOriginalPairedPointGroup
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (P₁ : Subgroup G) : Prop :=
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  letI := hU.normal
  letI := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
    c.count = 2 ∧
    (∀ i j, ∃ t : S, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j) ∧
    ∃ i j : Fin c.count, i ≠ j ∧
      markedV d.flag.flag.module ∈
        ((AddSubgroup.toSubgroup' (c.toSolvableFFFactors.factorFixedSpace
          ((ChapterB.baumann (S : Subgroup H)).map q) j).toAddSubgroup).map U.subtype).map H.subtype ∧
      P₁ = ((c.factor i).comap q).map H.subtype ⊔ ChapterB.baumann (T : Subgroup G)

/-- The opposite original solvable factor gives the first point-local group.
Its construction retains the original quotient preimage and the common Baumann
subgroup. Neither a local quotient nor a point-centralizing factor is assumed. -/
theorem exists_paired_point_group
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ∃ P₁ : Subgroup G, IsOriginalPairedPointGroup d hH P₁ ∧
      P₁ ≤ H ∧ P₁ ≤ Gv (markedV d.flag.flag.module) ∧
      ChapterB.baumann (T : Subgroup G) ≤ P₁ ∧
      ¬ P₁ ≤ normalizer (L : Set G) ∧
      (ChapterB.baumann (T : Subgroup G)).relIndex P₁ = 3 ∧
      Nonempty ((P₁ ⧸ pCore 2 P₁) ≃* Equiv.Perm (Fin 3)) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,hc,ht,hE,hpair,hn⟩ := source_solvable_paired_fixed_lines d hH hB hZ hs hz
  let D := c.toSolvableFFFactors
  let B := ChapterB.baumann (T : Subgroup G)
  let E := fun i => ((AddSubgroup.toSubgroup'
    (D.factorFixedSpace ((ChapterB.baumann (S : Subgroup H)).map q) i).toAddSubgroup).map
      U.subtype).map H.subtype
  let v := markedV d.flag.flag.module
  have hv : v ∈ V₂ := d.flag.flag.vector_mem
  have hvZ : v ∉ V₁ := d.flag.flag.vector_not_mem
  have hcomm (i j) : E j ≤ normalizer (E i : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    let := d.elementary
    intro x hx y hy
    exact congrArg V.subtype (mul_comm
      (⟨y,d.flag.two_le_V ((hE i).2.1 hy)⟩ : V)
      (⟨x,d.flag.two_le_V ((hE j).2.1 hx)⟩ : V))
  have hchoose : ∃ i j : Fin c.count, i ≠ j ∧ v ∈ E j := by
    let i : Fin c.count := ⟨0,by omega⟩
    let j : Fin c.count := ⟨1,by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
    have hvjoin : v ∈ E i ⊔ E j := (hpair i j hij).2.1.symm ▸ hv
    have hm : v ∈ (E i : Set G) * (E j : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ (hcomm i j)]
      exact hvjoin
    obtain ⟨a,ha,b,hb,hab⟩ := hm
    by_cases ha1 : a = 1
    · refine ⟨i,j,hij,?_⟩
      have he : b = v := by simpa only [ha1,one_mul] using hab
      exact he ▸ hb
    by_cases hb1 : b = 1
    · refine ⟨j,i,hij.symm,?_⟩
      have he : a = v := by simpa only [hb1,mul_one] using hab
      exact he ▸ ha
    exact (hvZ (hab ▸ ((hpair i j hij).2.2 a ha ha1 b hb hb1 ▸ mem_zpowers (a*b)))).elim
  obtain ⟨i,j,hij,hvj⟩ := hchoose
  let A := (c.factor i).comap q
  let F := A.map H.subtype
  have hFC : F ≤ Gv v := by
    obtain ⟨y,⟨u,hu,rfl⟩,huv⟩ := hvj
    rintro x ⟨a,ha,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←huv]
    have hfix : ρ (q a) (Additive.ofMul u) = Additive.ofMul u :=
      D.factor_fixes_other_support hij ⟨q a,ha⟩ hu.1
    have hh : MulAut.conj a (u : H) = (u : H) := by
      have he := congrArg (fun w : Additive U => (w.toMul : H)) hfix
      change ((NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) (q a)
          (Additive.ofMul u)).toMul : H) = (u : H) at he
      rw [NormalElementaryQuotient.representation_apply] at he
      exact he
    exact congrArg H.subtype (mul_inv_eq_iff_eq_mul.mp hh)
  have hBN : B ≤ normalizer (F : Set G) := by
    intro b hb
    exact ((hn i).ge hb).2
  have hBC : B ≤ Gv v :=
    (source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz v hv hvZ).le.trans inf_le_right
  have hk : q.ker = pCore 2 H := (QuotientGroup.ker_mk' C).trans
    (source_omega_centralizer_eq_twoCore d hH hB hZ hs)
  obtain ⟨_,_,hp,_,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hj
    rw [QuotientGroup.ker_mk'] at he
    exact le_top.trans he.ge
  have hpq := (ChapterB.minimalParabolic_reduced_image S hp q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hne).2
  have hgen := (ChapterB.offender_generation (S.mapSurjective (QuotientGroup.mk'_surjective C))
    hpq ρ ((isFFModule_iff_quadraticRatio_le_one ρ).mpr c.ratio_one.le)
      hU.quotient_pCore_eq_bot).2
  have hFM : ¬F ≤ normalizer (L : Set G) := factor_preimage_not_le q
    (QuotientGroup.mk'_surjective C) hH.1.1.2
    (hk ▸ pCore_isPGroup.le_sylow_of_normal S) D ht hgen
      (normalizer (L : Set G)) d.normalizes_L hH.1.2 i
  have hFA := factor_preimage_card q (QuotientGroup.mk'_surjective C)
    (hk ▸ pCore_isPGroup) D i
  have hcard : ∃ n, Nat.card F ∣ 3 * 2^n := by
    obtain ⟨n,hn⟩ := hFA.1
    exact ⟨n,by rwa [card_map_of_injective H.subtype_injective]⟩
  have hFtwo : ¬IsPGroup 2 F := fun hh => hFA.2
    (hh.of_equiv (A.equivMapOfInjective H.subtype H.subtype_injective).symm)
  let P₁ := F ⊔ B
  have hP₁c : P₁ ≤ Gv v := sup_le hFC hBC
  obtain ⟨P,hP⟩ := point_baumann_sylow d hH hB hZ hs hz
  change (P : Subgroup (Gv v)).map (Gv v).subtype = B at hP
  have hindex := normalized_cubic_join_index_of_card_dvd P (F.subgroupOf (Gv v))
    (by
      intro p hp
      apply mem_normalizer_iff.mpr
      intro a
      exact mem_normalizer_iff.mp (hBN (hP ▸ mem_map_of_mem (Gv v).subtype hp)) (a : G))
    (by
      obtain ⟨n,hn⟩ := hcard
      exact ⟨n,by rwa [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv]⟩)
    (fun hh => hFtwo (hh.of_equiv (subgroupOfEquivOfLe hFC)))
  have hi : B.relIndex P₁ = 3 := by
    have hm := relIndex_map_map_of_injective (P : Subgroup (Gv v))
      (F.subgroupOf (Gv v) ⊔ (P : Subgroup (Gv v))) (Gv v).subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hFC,hP] at hm
    exact hm.trans hindex
  have hP₁M : ¬P₁ ≤ normalizer (L : Set G) := fun hh => hFM (le_sup_left.trans hh)
  refine ⟨P₁,⟨c,hc,ht,i,j,hij,hvj,rfl⟩,sup_le (map_subtype_le _) (inf_le_left.trans hH.1.1.2),hP₁c,
    le_sup_right,hP₁M,hi,?_⟩
  let R := ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    : IsPGroup 2 (B.subgroupOf P₁)).toSylow (show ¬ 2 ∣ (B.subgroupOf P₁).index by change ¬2 ∣ B.relIndex P₁; rw [hi]; decide)
  apply sylow_index_three_core_quotient R hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal R)
  intro he
  change pCore 2 P₁ = B.subgroupOf P₁ at he
  have hn : (B.subgroupOf P₁).Normal := he ▸ inferInstance
  exact hP₁M (((normal_subgroupOf_iff_le_normalizer (show B ≤ P₁ from le_sup_right)).mp hn).trans hB)


/-- The actual source pair inside the nonsingular point centralizer has common
Sylow Baum(T), and its generated group is SQTK. -/
theorem exists_paired_point_goldschmidt_triple
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ∃ P₁ : Subgroup G, IsOriginalPairedPointGroup d hH P₁ ∧
      P₁ ≤ H ∧ P₁ ≤ Gv (markedV d.flag.flag.module) ∧
      ChapterB.baumann (T : Subgroup G) ≤ P₁ ∧
      ¬ P₁ ≤ normalizer (L : Set G) ∧
      let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
      let J := P₁ ⊔ P₂
      P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) ∧
      J ≤ Gv (markedV d.flag.flag.module) ∧
      Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G)) J ∧
      IsSQTK KnownSimple.IsKnownSimple J ∧
      ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) := by
  let v := markedV d.flag.flag.module
  let B := ChapterB.baumann (T : Subgroup G)
  let P₂ := Lv L v ⊔ B
  obtain ⟨P₁,hOriginal,hP₁H,hP₁C,hBP₁,hout,hi,he₁⟩ := exists_paired_point_group d hH hB hZ hs hz
  let J := P₁ ⊔ P₂
  have hP₂M : P₂ ≤ normalizer (L : Set G) :=
    sup_le ((residual_le_L d.flag.flag.module).trans L.le_normalizer)
      (inf_le_left.trans d.normalizes_L)
  have hBC : B ≤ Gv v :=
    (source_baumann_eq_flag_point_centralizer d hH hB hZ hs hz _
      d.flag.flag.vector_mem d.flag.flag.vector_not_mem).le.trans inf_le_right
  have hJC : J ≤ Gv v := sup_le hP₁C (sup_le ((map_subtype_le _).trans inf_le_right) hBC)
  have hBJ : B ≤ J := hBP₁.trans le_sup_left
  have hinter : P₁ ⊓ P₂ = B := by
    have hBI : B ≤ P₁ ⊓ P₂ := le_inf hBP₁ le_sup_right
    have hmult := relIndex_mul_relIndex B (P₁ ⊓ P₂) P₁ hBI inf_le_left
    rw [hi] at hmult
    have hp : (B.relIndex (P₁ ⊓ P₂) * (P₁ ⊓ P₂).relIndex P₁).Prime := hmult ▸ Nat.prime_three
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hI⟩ | ⟨_,hB⟩
    · exact (hout ((relIndex_eq_one.mp hI).trans (inf_le_right.trans hP₂M))).elim
    · exact le_antisymm (relIndex_eq_one.mp hB) hBI
  obtain ⟨P,hP⟩ := point_baumann_sylow d hH hB hZ hs hz
  change (P : Subgroup (Gv v)).map (Gv v).subtype = B at hP
  have hpc : ¬2 ∣ B.relIndex (Gv v) := by
    have hm := relIndex_map_map_of_injective (P : Subgroup (Gv v)) ⊤ (Gv v).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,hP,relIndex_top_right] at hm
    rw [hm]
    exact P.not_dvd_index
  have hpi : ¬2 ∣ B.relIndex J := by
    intro hh
    exact hpc (hh.trans (dvd_of_mul_right_eq _ (relIndex_mul_relIndex B J (Gv v) hBJ hJC)))
  let R := ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    : IsPGroup 2 (B.subgroupOf J)).toSylow hpi
  have hv2 : orderOf v = 2 := by
    apply orderOf_eq_prime _ (markedV_ne_one d.flag.flag.module)
    change (d.flag.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))^2 = 1
    rw [←map_pow]
    have hvpow : (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v)^2 = 1 := by decide +kernel
    rw [hvpow,map_one]
  have hsq : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJC)).mp
      ((d.hypothesis.qtke.involution_centralizer_sqtk hv2).subgroup (J.subgroupOf (Gv v)))
  refine ⟨P₁,hOriginal,hP₁H,hP₁C,hBP₁,hout,hinter,hJC,
    ⟨R,map_subgroupOf_eq_of_le hBJ⟩,hsq,?_⟩
  have hquot (X : Subgroup G) (hX : X ≤ J)
      (he : Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3))) :
      Nonempty ((X.subgroupOf J ⧸ pCore 2 (X.subgroupOf J)) ≃* Equiv.Perm (Fin 3)) := by
    let e := subgroupOfEquivOfLe hX
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans he.some⟩
  refine ⟨?_,hquot P₁ le_sup_left he₁,
    hquot P₂ le_sup_right (point_residual_baumann_core_quotient d hH hB hZ hs hz),?_⟩
  · apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right,←MonoidHom.range_eq_map,range_subtype]
  · refine ⟨R,?_⟩
    change (P₁ ⊓ P₂).subgroupOf J = B.subgroupOf J
    rw [hinter]

/-- The opening Goldschmidt construction in source 13.2.12 on its original
contrary core-free join, with the earlier Baumann bound and solvability explicit. -/
theorem coreFree_borel_join_point_goldschmidt_triple
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    ∃ P₁ : Subgroup G, IsOriginalPairedPointGroup d hH P₁ ∧
      P₁ ≤ H ∧ P₁ ≤ Gv (markedV d.flag.flag.module) ∧
      ChapterB.baumann (T : Subgroup G) ≤ P₁ ∧
      ¬ P₁ ≤ normalizer (L : Set G) ∧
      let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
      let J := P₁ ⊔ P₂
      P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) ∧
      J ≤ Gv (markedV d.flag.flag.module) ∧
      Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G)) J ∧
      IsSQTK KnownSimple.IsKnownSimple J ∧
      ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) :=
  exists_paired_point_goldschmidt_triple d hH hB hZ hs
    (center_eq_bot_of_borel_join_core_eq_bot d hH hZ hcore)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
