module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection
public import Theory.SpecificGroups.GL2.ThreeSolvable

/-!
# Relative embeddings in odd prime ternary carriers

A perfect subgroup with binary PSL₂ two-core quotient in odd PSL₃ or
PSU₃ has a nontrivial two-core: otherwise its full normalizing Sylow
contradicts the faithful Sylow order calculation. The ambient two-rank
bound supplies a central involution. Its actual involution centralizer
lifts the perfect subgroup through a cubic central kernel into prime SL₂;
Dickson recognition makes this subgroup quasisimple. The binary central
cover calculation then forces degree two and the actual SL₂(5) cover.
The full Sylow normalizer forces the containing prime to be five.

For the special linear and unitary coverings, the central projection
preserves the smaller binary section because its central kernel maps
trivially to that centerless section. Restricting the original full Sylow
to K and mapping through K/O₂(K) retains the smaller intrinsic two-core.
Both flag normalizers and arbitrary nontrivial U ≤ V₁ are included.

This extends the A₅-only centralizer argument in
ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection to the original
binary parameter; it does not assume field four or quasisimplicity of
the smaller image. The preceding quotient models belong to
qt-d-1222-natural-flag-cartan and are discharged by
qt-d-1222-natural-local-geometry. Refinement.OddTernary applies this branch
at both normalizers; the relative-components owner retains full assembly.
Source: Aschbacher--Smith A.3.12(9), A.3.14 and 11.1.1--11.1.2,
printed pp.47--50,761--765, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.OddTernary
variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] [Nontrivial K]

omit [Finite K] in
private theorem quasisimple_of_prime_sl2_embedding
    {F : Type*} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : Nat.card F = p) (i : K →* SL(2,F)) (hi : Function.Injective i)
    : IsQuasisimple K := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hc, ZMod.card])
  let f := (GorensteinWalter.sl2RingEquiv a).toMonoidHom.comp i
  have hf : Function.Injective f := (GorensteinWalter.sl2RingEquiv a).injective.comp hi
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  have hlarge : 3 < p := by
    by_contra hh
    have he : p = 3 := by have := hp.two_le; have := Nat.odd_iff.mp ho; omega
    have hs : Group.IsSolvable SL(2,ZMod 3) := by
      let : Group.IsSolvable (GL (Fin 2) (ZMod 3)) :=
        Matrix.GeneralLinearGroup.three_isSolvable
      exact Group.isSolvable_of_isSolvable_injective
        (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ZMod 3))
    let : Group.IsSolvable SL(2,ZMod p) := he ▸ hs
    exact Group.IsPerfect.not_isSolvable K
      (Group.isSolvable_of_isSolvable_injective hf)
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : Nontrivial f.range := e.symm.nontrivial
  rcases ChapterA.RankActions.primePerfectSL2Recognition p hlarge f.range
    inferInstance inferInstance with hfull | ⟨_,hfive⟩
  · obtain ⟨b⟩ := hfull
    let : Fact (3 < Nat.card (ZMod p)) := ⟨by simpa using hlarge⟩
    exact IsQuasisimple.of_mulEquiv (e.trans b).symm
  · obtain ⟨b⟩ := hfive
    let : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩
    exact IsQuasisimple.of_mulEquiv (e.trans b).symm

omit [Finite K] in
private theorem quasisimple_of_cubic_centralizer
    {V H F E : Type*} [Group V] [Group H] [Field F] [Field E] [Finite E]
    (ρ : V →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (f : V →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center V)
    (h3 : ∀ v ∈ f.ker, v ^ 3 = 1)
    (d : (GeneralLinearGroup.det.comp ρ).ker ≃* SL(2,E))
    (j : K →* H) (hj : Function.Injective j)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hE : Nat.card E = p)
    : IsQuasisimple K := by
  let e : K ≃* j.range := MonoidHom.ofInjective hj
  let : Group.IsPerfect j.range := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hn : ¬ IsMulCommutative V := by
    intro ha
    have hh : IsMulCommutative H := IsMulCommutative.of_comm (fun x y => by
      obtain ⟨x,rfl⟩ := hf x
      obtain ⟨y,rfl⟩ := hf y
      rw [←map_mul,←map_mul,ha.is_comm.comm x y])
    exact Group.IsPerfect.not_isMulCommutative K (IsMulCommutative.of_comm
      (fun x y => hj (by rw [map_mul,map_mul,hh.is_comm.comm])))
  let D := (GeneralLinearGroup.det.comp ρ).ker
  let a : D ≃* D.map f := MulEquiv.ofBijective (f.subgroupMap D)
    ⟨Theory.SpecificGroups.OddThreeLevi.determinant_kernel_injective ρ hρ hn f hk h3,
      f.subgroupMap_surjective D⟩
  have hB : j.range ≤ D.map f :=
    Theory.SpecificGroups.OddThreeLevi.perfect_subgroup_le_det_kernel_image ρ f hf j.range
  let i := d.toMonoidHom.comp (a.symm.toMonoidHom.comp
    ((inclusion hB).comp e.toMonoidHom))
  have hi : Function.Injective i := d.injective.comp
    (a.symm.injective.comp ((inclusion_injective hB).comp e.injective))
  exact quasisimple_of_prime_sl2_embedding hp ho hE i hi


private def centralizer_embedding {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G)
    (hz : B ≤ centralizer ({z} : Set G)) :
    B →* centralizer ({e z} : Set H) :=
  (e.toMonoidHom.comp B.subtype).codRestrict _ (by
    intro b
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      ← map_mul] using congrArg e (mem_centralizer_singleton_iff.mp (hz b.property)))

private theorem centralizer_embedding_injective {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) (z : G) (hz : B ≤ centralizer ({z} : Set G)) :
    Function.Injective (centralizer_embedding e B z hz) := by
  intro a b h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

private theorem section_quasisimple_of_involution
    {G : Type*} [Group G] [Finite G] (B : Subgroup G) [Group.IsPerfect B] [Nontrivial B]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p)
    (z : G) (hz : orderOf z = 2) (hBz : B ≤ centralizer ({z} : Set G)) :
    IsQuasisimple B := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have h2 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho
      (k := 1) (by simpa using hF)
    obtain ⟨f,hf,hk,h3⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection
      (e z) ((e.orderOf_eq z).trans hz) h2
    exact quasisimple_of_cubic_centralizer (MonoidHom.id _) Function.injective_id
      f hf hk h3 (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm
      (centralizer_embedding e B z hBz) (centralizer_embedding_injective e B z hBz)
      hp ho hF
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    obtain ⟨f,hf,hk,h3⟩ := SU3.OddCubicCentralizer.surjection p ho F J hF hc
      (e z) ((e.orderOf_eq z).trans hz)
    let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
    let d : J2.unitaryDet.ker ≃* SL(2,GaloisField p 1) :=
      J2.unitaryDetKernelEquiv.trans (ABG.specialUnitaryTwo_equiv_sl2 p 1 ho one_ne_zero)
    exact quasisimple_of_cubic_centralizer J2.unitarySubgroup.subtype Subtype.val_injective
      f hf hk h3 d (centralizer_embedding e B z hBz)
      (centralizer_embedding_injective e B z hBz) hp ho
      (by simpa using GaloisField.card p 1 one_ne_zero)

private theorem odd_three_rank {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) :
    primeRank 2 G ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hc



variable {G : Type*} [Group G] [Finite G]

/-- The actual binary two-core section forces both field parameters in
an odd prime projective ternary carrier. -/
theorem projective_parameters (S : Sylow 2 G) (B : Subgroup G)
    [Group.IsPerfect B] (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 3 p ∨ ClassicalGroup.IsPSU G 3 p) :
    n = 2 ∧ p = 5 := by
  have hb : ¬ ClassicalGroup.IsPSL B 2 (2^n) := by
    intro h
    rcases hm with hm | hm
    · exact (not_odd_three_binary_intrinsic S B hn h hSB hp ho false).1 hm
    · exact (not_odd_three_binary_intrinsic S B hn h hSB hp ho true).1 hm
  have hcore : pCore 2 B ≠ ⊥ := by
    intro hz
    let e : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    exact hb (hsmall.of_mulEquiv e.symm)
  have hne : B ≠ ⊥ := by
    intro he
    subst B
    exact hcore (Subsingleton.elim _ _)
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hne
  obtain ⟨z,_,hz,hBz⟩ := exists_involution_centralized_by_perfect_sup_sylow S B
    (odd_three_rank hp ho hm) hSB hcore
  let : IsQuasisimple B := section_quasisimple_of_involution B hp ho hm z hz
    (le_sup_left.trans hBz)
  obtain ⟨hn2,hcover⟩ := (quasisimple_binary_core_models hn hsmall).resolve_left hb
  refine ⟨hn2,?_⟩
  rcases hm with hm | hm
  · exact odd_three_sl2_five_parameter S B hcover hSB hp ho false (.inl hm)
  · exact odd_three_sl2_five_parameter S B hcover hSB hp ho true (.inl hm)

private theorem central_kernel_section {H : Type*} [Group H] [Finite H]
    (q : G →* H) (hker : q.ker ≤ center G) (B : Subgroup G)
    {n : ℕ} (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) :
    ClassicalGroup.IsPSL (B.map q ⧸ pCore 2 (B.map q)) 2 (2^n) := by
  have hk : (q.subgroupMap B).ker ≤ pCore 2 B := by
    intro b hb
    have hc : b ∈ center B := mem_center_iff.mpr (fun a => Subtype.ext
      (mem_center_iff.mp (hker (congrArg Subtype.val hb)) a))
    have hz : QuotientGroup.mk' (pCore 2 B) b ∈ center (B ⧸ pCore 2 B) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) a
      simpa only [← map_mul] using congrArg (QuotientGroup.mk' (pCore 2 B))
        (mem_center_iff.mp hc a)
    rw [binary_center_eq_bot hm] at hz
    have hh : b ∈ (QuotientGroup.mk' (pCore 2 B)).ker := hz
    simpa only [QuotientGroup.ker_mk'] using hh
  let e := (q.subgroupMap B).quotientPCoreEquivOfSurjective
    (q.subgroupMap_surjective B) (pCore_isPGroup.to_le hk)
  exact hm.of_mulEquiv e.symm

private theorem central_surjection_parameters {H : Type*} [Group H] [Finite H]
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker ≤ center G)
    (S : Sylow 2 G) (B : Subgroup G) [Group.IsPerfect B]
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL H 3 p ∨ ClassicalGroup.IsPSU H 3 p) :
    n = 2 ∧ p = 5 := by
  let : Group.IsPerfect (B.map q) := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap B) (q.subgroupMap_surjective B)
  exact projective_parameters (S.mapSurjective hq) (B.map q)
    ((map_mono hSB).trans (B.le_normalizer_map q)) hn
    (central_kernel_section q hk B hsmall) hp ho hm

omit [Finite G] in
private theorem kernel_central_comp {H A : Type*} [Group H] [Group A]
    (e : G ≃* A) (q : A →* H) (hk : q.ker ≤ center A) :
    (q.comp e.toMonoidHom).ker ≤ center G := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul,MulEquiv.coe_toMonoidHom] using mem_center_iff.mp (hk hx) (e y)

/-- Both signs and both special/projective coverings retain the smaller
two-core and force precisely the source field-four/prime-five row. -/
theorem signed_parameters (S : Sylow 2 G) (B : Subgroup G)
    [Group.IsPerfect B] (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign G u 3 p ∨
      Chapter1.Section02.LocalModels.IsSLSign G u 3 p) : n = 2 ∧ p = 5 := by
  rcases hm with hm | hm
  · apply projective_parameters S B hSB hn hsmall hp ho
    cases u with
    | false => exact .inl hm
    | true => exact .inr hm
  · cases u with
    | false =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let q := (PSL3.projection F).comp e.toMonoidHom
      exact central_surjection_parameters q
        ((PSL3.projection_surjective F).comp e.surjective)
        (kernel_central_comp e (PSL3.projection F) (by rw [PSL3.projection_ker]))
        S B hSB hn hsmall hp ho
        (.inl ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
    | true =>
      obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let q := J.specialToProjective.comp e.toMonoidHom
      have hq := J.specialToProjective_surjective.comp e.surjective
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective q hq
      exact central_surjection_parameters q hq
        (kernel_central_comp e J.specialToProjective J.specialToProjective_ker_le_center)
        S B hSB hn hsmall hp ho
        (.inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨MulEquiv.refl _⟩⟩)


/-- Transport the signed ternary marking through an actual group equivalence. -/
private theorem signed_transport {A H : Type*} [Group A] [Group H]
    (e : A ≃* H) (u : Bool) (p : ℕ)
    (h : Chapter1.Section02.LocalModels.IsPSLSign H u 3 p ∨
      Chapter1.Section02.LocalModels.IsSLSign H u 3 p) :
    Chapter1.Section02.LocalModels.IsPSLSign A u 3 p ∨
      Chapter1.Section02.LocalModels.IsSLSign A u 3 p := by
  cases u with
  | false =>
    rcases h with h | h
    · exact .inl (h.of_mulEquiv e)
    · obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
      exact .inr ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩
  | true =>
    rcases h with h | h
    · obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := h
      exact .inl ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.trans a⟩⟩
    · obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := h
      exact .inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.trans a⟩⟩

private theorem local_parameters
    (P : Sylow 2 G) {B K : Subgroup G} [Group.IsPerfect B]
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hmodel : Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 p ∨
      Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 p) :
    n = 2 ∧ p = 5 := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  let C := B.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  have hQC : (Q : Subgroup K) ≤ normalizer (C : Set K) := by
    rw [hQ,← subgroupOf_normalizer_eq hBK]
    exact comap_mono hPB
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let d := subgroupOfEquivOfLe hBK
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let a := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  let : Group.IsPerfect (C.map q) := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap C) (q.subgroupMap_surjective C)
  exact signed_parameters (Q.mapSurjective (QuotientGroup.mk'_surjective _))
    (C.map q) ((map_mono hQC).trans (C.le_normalizer_map q)) hn
    (hm.of_mulEquiv (a.symm.trans dq)) hp ho u hmodel

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.OddTernary

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The literal relative component, with the full Sylow and the original
smaller two-core, has field four and ternary prime five. -/
theorem relative_odd_ternary_parameters
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hmodel : IsPSLSign (K ⧸ pCore 2 K) u 3 p ∨ IsSLSign (K ⧸ pCore 2 K) u 3 p) :
    n = 2 ∧ p = 5 := by
  obtain ⟨P₀,hP₀⟩ := hP
  have hBH : B ≤ H := hBK.trans hK.1
  have hnB : (P₀ : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    intro a ha b
    change (b : G) ∈ B ↔ (a : G) * (b : G) * (a : G)⁻¹ ∈ B
    exact hPB (hP₀ ▸ mem_map_of_mem H.subtype ha) b
  let b := subgroupOfEquivOfLe hBH
  let k := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let : Group.IsPerfect B := by
    let := hB.1.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsPerfect (B.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  exact OddTernary.local_parameters P₀ (B := B.subgroupOf H) (K := K.subgroupOf H)
    hK.2 (comap_mono hBK) hnB hn
    (hm.of_mulEquiv bq) hp ho u (OddTernary.signed_transport kq u p hmodel)

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both original normalizers retain the field-four and prime-five restrictions. -/
theorem flag_odd_ternary_parameters (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hmodel : IsPSLSign (K ⧸ pCore 2 K) u 3 p ∨ IsSLSign (K ⧸ pCore 2 K) u 3 p) :
    S.field.degree = 2 ∧ p = 5 := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) :=
    f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_odd_ternary_parameters hs (flag_mem_local_of_model D S f i hm)
    hK hLK (f.sylow_normalizes_Li i) S.nonbinary hm hp ho u hmodel

/-- The signed ternary alternative of 11.1.1 at either original normalizer. -/
theorem flag_component_alternative_of_odd_ternary (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hmodel : IsPSLSign (K ⧸ pCore 2 K) u 3 p ∨ IsSLSign (K ⧸ pCore 2 K) u 3 p) :
    ComponentAlternative (f.Li i) K S.field.degree := by
  obtain ⟨hn,rfl⟩ := flag_odd_ternary_parameters D S f i hm hK hLK hp ho u hmodel
  exact .four hn (.three u hmodel)

/-- The arbitrary-subspace clause keeps the literal N_T(U) Sylow hypothesis. -/
theorem subspace_component_alternative_of_odd_ternary
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hmodel : IsPSLSign (K ⧸ pCore 2 K) u 3 p ∨ IsSLSign (K ⧸ pCore 2 K) u 3 p) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  obtain ⟨hn,rfl⟩ := relative_odd_ternary_parameters hSyl hlocalP hK hLK
    (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm hp ho u hmodel
  exact .four hn (.three u hmodel)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
