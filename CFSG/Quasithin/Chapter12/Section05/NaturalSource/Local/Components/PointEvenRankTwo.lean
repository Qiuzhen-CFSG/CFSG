module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointRankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LinearThreeLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.SpecificGroups.G2.BinarySolvableSylowOvergroups
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.Triality.OddSupplement
public import Theory.SpecificGroups.SL2.BinaryThreeSection
public import Theory.SpecificGroups.ReeF4.OddSupplement
public import Theory.SpecificGroups.ReeF4.BinaryThreeSection
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSmallModels
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The characteristic-two rank-two point-component sieve

For an even linear-three, symplectic-four or G₂ quotient, a proper local
C-component is a conjugate parabolic residual. Its SL₂ core quotient cannot
have the order 168 of the original point residual. For genuine triality and
Ree quotients, full-Sylow placement puts a proper local join in an actual
root parabolic. Perfectness removes the complementary torus. The surviving
binary SL₂ quotient is incompatible with the order-four elements of the
original SL₃(2) section; the Ree Suzuki parabolic is three-free. This includes
the binary triality endpoint and retains the original two-group kernels.
The same parabolic quotient argument handles the even SL₃ covers; the
even SU₃ covers use the checked rank-one non-enlargement theorem.
The small derived G₂ and Tits carriers have solvable proper Sylow overgroups,
and the derived symplectic endpoint is the already excluded A₆ quotient.

The entire RankTwoTheoremC catalogue and both signs of the even classical
cover rows therefore force K₁ = L₁. Transport
uses the literal G₁/O₂(G₁) projection, its restricted full Sylow, and the
actual smaller core quotient. The original containing C-component gives
uniqueness of its intrinsic C-components, so the parabolic argument needs
no new simplicity hypothesis for the model carrier.

PointCore.PointEvenRankTwo connects this result to all four components,
both normalizer containments, point-core containment, point control and
generation one. The remaining point-model sieve, general normalizers and
quasisimple escape remain with qt-d-1251-local; qt-d-1251-source owns final
exterior assembly and the discharge of its earlier-source inputs.
Source: Aschbacher--Smith 12.5.3, pp.817--818, and A.3.12, pp.47--48.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem sl2_card_ne {F : Type*} [Field F] [Finite F] :
    Nat.card SL(2,F) ≠ 168 := by
  intro he
  rw [GorensteinWalter.sl2_card_formula] at he
  have hq : Nat.card F ≤ 5 := by
    by_contra! hq
    have hq6 : 6 ≤ Nat.card F := by omega
    have hh : 35 ≤ Nat.card F ^ 2 - 1 := by
      have hsq := Nat.pow_le_pow_left hq6 2
      omega
    have hh' := Nat.mul_le_mul hq6 hh
    omega
  interval_cases h : Nat.card F <;> simp at he

private theorem core_card_ne_of_equiv {A F : Type*} [Group A] [Field F] [Finite F]
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F)) : Nat.card (A ⧸ pCore 2 A) ≠ 168 := by
  rw [Nat.card_congr e.toEquiv]
  exact sl2_card_ne

private theorem linear_local_eq_top {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hc : Nat.card (B ⧸ pCore 2 B) = 168) : B = ⊤ := by
  by_contra hp
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hn S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc' : Nat.card ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) = 168 :=
    (Nat.card_congr aq.toEquiv).symm.trans hc
  rcases hg with hg | hg
  · rw [hg] at hc'
    exact core_card_ne_of_equiv (Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F) hc'
  · rw [hg] at hc'
    exact core_card_ne_of_equiv (Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F) hc'

private theorem special_linear_local_eq_top {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hc : Nat.card (B ⧸ pCore 2 B) = 168) : B = ⊤ := by
  by_contra hp
  obtain ⟨g,hg⟩ := FiveLocalFF.special_linear_three_local_placement hF hn S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc' : Nat.card ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) = 168 :=
    (Nat.card_congr aq.toEquiv).symm.trans hc
  rcases hg with hg | hg
  · rw [hg] at hc'
    exact core_card_ne_of_equiv (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F) hc'
  · rw [hg] at hc'
    exact core_card_ne_of_equiv (Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F) hc'

private theorem symplectic_local_eq_top {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hB : B ∈ localCComponents S) (hc : Nat.card (B ⧸ pCore 2 B) = 168) : B = ⊤ := by
  by_contra hp
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hn S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc' : Nat.card ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) = 168 :=
    (Nat.card_congr aq.toEquiv).symm.trans hc
  rcases hg with hg | hg
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn) hc'
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn) hc'

private theorem g2_local_eq_top {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F)) (B : Subgroup (Atlas.G2.Model F))
    (hB : B ∈ localCComponents S) (hc : Nat.card (B ⧸ pCore 2 B) = 168) : B = ⊤ := by
  by_contra hp
  obtain ⟨g,hg⟩ := FiveLocalFF.G2.local_placement hq S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hc' : Nat.card ((B.map (MulAut.conj g).toMonoidHom) ⧸
      pCore 2 (B.map (MulAut.conj g).toMonoidHom)) = 168 :=
    (Nat.card_congr aq.toEquiv).symm.trans hc
  rcases hg with hg | hg
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (local₁CoreQuotientEquivPSL.trans longSLEquivPSL.symm) hc'
  · rw [hg] at hc'
    exact core_card_ne_of_equiv
      (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm) hc'

private theorem local_perfect {X : Type*} [Group X] (S : Subgroup X)
    {B : Subgroup X} (hB : B ∈ localCComponents S) : Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

private theorem local_join_ne_top {X : Type*} [Group X]
    (S : Subgroup X) {B : Subgroup X} (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (hcomp : ∀ J : Subgroup X, J.IsCComponent → J = ⊤) : B ⊔ S ≠ ⊤ := by
  intro ht
  have hc : B.IsCComponent := by
    change (B.subgroupOf (B ⊔ S)).IsCComponent at hB
    rw [ht] at hB
    simpa only [map_subgroupOf_eq_of_le le_top] using hB.map_subtype (.top)
  exact hp (hcomp B hc)

private theorem triality_perfect_le_local (P : Triality.Standard.Parameters)
    (hp : P.prime = 2) (a : Triality.Standard.Parabolics.Node)
    (B : Subgroup (Triality.Standard.Carrier P)) [Group.IsPerfect B]
    (hB : B ≤ Triality.Standard.Parabolics.parabolic P a) :
    B ≤ Triality.Standard.Parabolics.localFactor P a := by
  let X := B.subgroupOf (Triality.Standard.Parabolics.parabolic P a)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let N := (Triality.Standard.Parabolics.localFactor P a).subgroupOf
    (Triality.Standard.Parabolics.parabolic P a)
  let : IsCyclic (Triality.Standard.Parabolics.parabolic P a ⧸ N) :=
    Triality.Standard.Parabolics.parabolic_quotient_isCyclic P hp a
  let : CommGroup (Triality.Standard.Parabolics.parabolic P a ⧸ N) := IsCyclic.commGroup
  have hh := le_of_isPerfect_of_solvable_quotient X N
  intro x hx
  exact hh (show (⟨x,hB hx⟩ : Triality.Standard.Parabolics.parabolic P a) ∈ X from hx)

private theorem triality_local_eq_top (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (Triality.Standard.BinaryCarrier n hn))
    (B : Subgroup (Triality.Standard.BinaryCarrier n hn))
    (hB : B ∈ localCComponents S)
    (hcomp : ∀ J : Subgroup (Triality.Standard.BinaryCarrier n hn), J.IsCComponent → J = ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) : B = ⊤ := by
  by_contra hp
  let P := Triality.Standard.binaryParameters n hn
  let : Group.IsPerfect B := local_perfect (X := Triality.Standard.BinaryCarrier n hn) (S : Subgroup (Triality.Standard.BinaryCarrier n hn)) hB
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (Triality.Standard.BinaryCarrier n hn)) S
    (Triality.Standard.Parabolics.unipotentSylow P rfl)
  change (S : Subgroup (Triality.Standard.BinaryCarrier n hn)).map a.toMonoidHom = Triality.Standard.Parabolics.unipotent P at hS
  let H := B ⊔ (S : Subgroup (Triality.Standard.BinaryCarrier n hn))
  have hH : H.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply local_join_ne_top (S : Subgroup (Triality.Standard.BinaryCarrier n hn)) hB hp hcomp
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨j,hj⟩ := Triality.Standard.OddSupplement.le_parabolic n hn
    (H.map a.toMonoidHom) (hS ▸ map_mono le_sup_right) hH
  let A := B.map a.toMonoidHom
  let : Group.IsPerfect A := Group.IsPerfect.map a.toMonoidHom
  have hAL := triality_perfect_le_local P rfl j A ((map_mono le_sup_left).trans hj)
  let f : B →* Triality.Standard.Parabolics.localFactor P j :=
    (a.toMonoidHom.comp B.subtype).codRestrict _
      (fun b => hAL (mem_map_of_mem a.toMonoidHom b.property))
  have hf : Function.Injective f := fun b c he => Subtype.ext
    (a.injective (congrArg Subtype.val he))
  have hk : IsPGroup 2 f.ker := by
    rw [f.ker_eq_bot_iff.mpr hf]
    exact IsPGroup.of_card (n := 0) (by simp)
  let π := eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  have hπ : Function.Surjective π := eB.surjective.comp (QuotientGroup.mk'_surjective _)
  cases j with
  | arms =>
    exact Matrix.SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient π hπ f hk
      ((Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (Triality.Standard.ExtensionField P)).symm)
  | central =>
    exact Matrix.SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient π hπ f hk
      ((Triality.Standard.Parabolics.localFactorCentralQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm)

private theorem ree_local_eq_top (m : ℕ) (hm : 1 ≤ m)
    (S : Sylow 2 (ReeF4.Model m)) (B : Subgroup (ReeF4.Model m))
    (hB : B ∈ localCComponents S)
    (hcomp : ∀ J : Subgroup (ReeF4.Model m), J.IsCComponent → J = ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) : B = ⊤ := by
  by_contra hp
  let : Group.IsPerfect B := local_perfect (X := ReeF4.Model m) (S : Subgroup (ReeF4.Model m)) hB
  obtain ⟨_,a,_,hS⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (ReeF4.Model m)) S (ReeF4.Parabolics.ThreeSylowContainment.positiveSylow m)
  rw [ReeF4.Parabolics.ThreeSylowContainment.positiveSylow_coe] at hS
  let H := B ⊔ (S : Subgroup (ReeF4.Model m))
  have hH : H.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply local_join_ne_top (S : Subgroup (ReeF4.Model m)) hB hp hcomp
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨j,hj⟩ := ReeF4.OddSupplement.le_parabolic m hm
    (H.map a.toMonoidHom) (hS ▸ map_mono le_sup_right) hH
  have hBP : B.map a.toMonoidHom ≤ ReeF4.ConverseParabolics.parabolic m j :=
    (map_mono le_sup_left).trans hj
  let f : B →* ReeF4.ConverseParabolics.parabolic m j :=
    (a.toMonoidHom.comp B.subtype).codRestrict _
      (fun b => hBP (mem_map_of_mem a.toMonoidHom b.property))
  have hf : Function.Injective f := fun b c he => Subtype.ext
    (a.injective (congrArg Subtype.val he))
  exact ReeF4.ConverseParabolics.no_binary_three_quotient_in_parabolic
    (eB.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
    (eB.surjective.comp (QuotientGroup.mk'_surjective _)) hm j f hf

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private theorem point_eq_of_binary_three_locals {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {X : Type*} [Group X] [Finite X] (eX : (K ⧸ pCore 2 K) ≃* X)
    (hX : ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ localCComponents S →
      (∀ J : Subgroup X, J.IsCComponent → J = ⊤) →
      ((B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) → B = ⊤) : s.marking.Li 1 = K := by
  let H := s.marking.Gi 1
  let B := (s.marking.Li 1).subgroupOf H
  let C := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hB : B ∈ Chapter1.L H (T.subtype s.sylow_le_G₁) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf s.sylow_le_G₁ (s.marking.Li_le_Gi 1)).mp
        ⟨s.marking.Li_le_Gi 1,s.Li_mem_local 1 (.inl rfl)⟩
  have hBq : B.map q ∈ localCComponents
      ((T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB
  have hBC : B.map q ≤ C.map q := map_mono (comap_mono hLK)
  obtain ⟨S,_,hl⟩ := exists_local_sylow_restriction _ hBq hBC (hK.2.map_quotient _).subnormal
  let a := subgroupOfEquivOfLe hK.1
  let e : C.map q ≃* X := (cComponentTwoCoreQuotientEquiv hK.2).symm.trans
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eX)
  let A := (B.map q).subgroupOf (C.map q)
  let b := subgroupOfEquivOfLe hBC
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let c := e.subgroupMap A
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let d : (B.map q ⧸ pCore 2 (B.map q)) ≃* SL(3,ZMod 2) :=
    ((s.pointCoreImageHom (s.marking.Li 1) (s.marking.Li_le_Gi 1)).pCoreQuotientEquiv
      (s.pointCoreImageHom_surjective _ _) (s.pointCoreImageHom_ker_isPGroup _ _)).symm.trans
        (s.marking.LiCoreEquiv 1 (.inl rfl))
  let hc := cq.symm.trans (bq.trans d)
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hcomp : ∀ J : Subgroup X, J.IsCComponent → J = ⊤ := by
    intro J hJ
    have ht := (hK.2.map_quotient _).eq_top_of_isCComponent (hJ.map_equiv e.symm)
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    rw [ht,map_top_of_surjective _ e.symm.surjective]
  have ht := hX (S.mapSurjective (f := e.toMonoidHom) e.surjective) (A.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom) hcomp hc
  have hAtop : A = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [ht,map_top_of_surjective _ e.surjective]
  have he : B.map q = C.map q := le_antisymm hBC (subgroupOf_eq_top.mp hAtop)
  have hk : q.ker ≤ (T.subtype s.sylow_le_G₁ : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal _
  have hh := local_cComponent_eq_of_map_eq hB.1 hK.2 (comap_mono hLK) q hk he
  exact (map_subgroupOf_eq_of_le (s.marking.Li_le_Gi 1)).symm.trans
    ((congrArg (map H.subtype) hh).trans (map_subgroupOf_eq_of_le hK.1))

/-- Every even projective linear-three point model retains the original residual. -/
theorem point_component_eq_of_even_linear_three {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    s.marking.Li 1 = K := by
  by_cases hn1 : n = 1
  · exact s.point_component_eq_of_binary_three hK hLK (by simpa [hn1] using hm)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact s.point_eq_of_binary_three_locals hK hLK e (fun S B hB _ eB =>
    linear_local_eq_top hF (by omega) S B hB
      ((Nat.card_congr eB.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card))

/-- An even symplectic-four quotient cannot strictly enlarge the point residual. -/
theorem point_component_eq_of_even_symplectic {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    s.marking.Li 1 = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  exact s.point_eq_of_binary_three_locals hK hLK a (fun S B hB _ eB =>
    symplectic_local_eq_top hF (by omega) S B hB
      ((Nat.card_congr eB.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card))

/-- The even G₂ point models force equality through the actual restricted Sylow. -/
theorem point_component_eq_of_even_g2 {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At (K ⧸ pCore 2 K) (2 ^ n)) :
    s.marking.Li 1 = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
  exact s.point_eq_of_binary_three_locals hK hLK e (fun S B hB _ eB =>
    g2_local_eq_top hq S B hB
      ((Nat.card_congr eB.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card))

/-- Even special-linear three-space covers also force equality at the original point. -/
theorem point_component_eq_of_even_special_linear_three {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {n : ℕ} (hn : 0 < n)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    s.marking.Li 1 = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  by_cases hn1 : n = 1
  · exact s.point_component_eq_of_solvable_sylow_overgroups hK hLK
      (isSolvable_proper_sylow_overgroup_of_equiv e
        (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two (by simpa [hn1] using hF)))
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact s.point_eq_of_binary_three_locals hK hLK e (fun S B hB _ eB =>
    special_linear_local_eq_top hF (by omega) S B hB
      ((Nat.card_congr eB.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card))

/-- Both signs of the even classical three-cover catalogue force equality at the point. -/
theorem point_component_eq_of_even_classical_cover {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {n : ℕ} (hn : 0 < n) (unitary : Bool)
    (hm : Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) unitary 3 (2 ^ n)) :
    s.marking.Li 1 = K := by
  cases unitary with
  | false => exact s.point_component_eq_of_even_special_linear_three hK hLK hn hm
  | true => exact s.point_component_eq_of_binary_unitary_three hK hLK hn hm

/-- The small derived G₂ carrier has no strict point-component enlargement. -/
theorem point_component_eq_of_binary_g2_derived {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    s.marking.Li 1 = K :=
  s.point_component_eq_of_solvable_sylow_overgroups hK hLK
    (isSolvable_proper_sylow_overgroup_of_equiv e Atlas.G2.BinaryDerived.solvableSylowOvergroups)

/-- The Tits carrier also forces equality of the actual embedded point subgroups. -/
theorem point_component_eq_of_tits {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Tits.ParrottGroup) : s.marking.Li 1 = K :=
  s.point_component_eq_of_solvable_sylow_overgroups hK hLK
    (isSolvable_proper_sylow_overgroup_of_equiv e Tits.ProperSylowOvergroups.solvableSylowOvergroups)


/-- Genuine triality quotients, including the binary endpoint, cannot enlarge L₁. -/
theorem point_component_eq_of_even_triality {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {n : ℕ} (hn : 0 < n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ pCore 2 K)) :
    s.marking.Li 1 = K := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn).mp hm
  exact s.point_eq_of_binary_three_locals hK hLK e (triality_local_eq_top n hn)

/-- The actual Ree carrier gives no strict point-component enlargement. -/
theorem point_component_eq_of_ree {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    {m : ℕ} (hm : 1 ≤ m) (e : (K ⧸ pCore 2 K) ≃* ReeF4.Model m) :
    s.marking.Li 1 = K :=
  s.point_eq_of_binary_three_locals hK hLK e (ree_local_eq_top m hm)

/-- Every characteristic-two rank-two row in the source catalogue forces K₁ = L₁. -/
theorem point_component_eq_of_even_rank_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K)) :
    s.marking.Li 1 = K := by
  cases hm with
  | linear n hn hm => exact s.point_component_eq_of_even_linear_three hK hLK (by omega) hm
  | symplectic n hn hm => exact s.point_component_eq_of_even_symplectic hK hLK hn hm
  | g2 n hn hm => exact s.point_component_eq_of_even_g2 hK hLK hn hm
  | triality n hn hm => exact s.point_component_eq_of_even_triality hK hLK (by omega) hm
  | ree m hm he =>
    obtain ⟨e⟩ := (ReeF4.exists_localBlockInput_mulEquiv_iff _ m).mp he
    exact s.point_component_eq_of_ree hK hLK hm e
  | symplectic_derived he =>
    exact (s.point_component_not_alternating h hK hLK hN (by omega : 5 ≤ 6 ∧ 6 ≤ 8)
      ⟨he.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩).elim
  | g2_derived he => exact s.point_component_eq_of_binary_g2_derived hK hLK he.some
  | tits he => exact s.point_component_eq_of_tits hK hLK he.some

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
