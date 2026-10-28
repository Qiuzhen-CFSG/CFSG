module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Outer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Geometry
public import Theory.SpecificGroups.BinaryLinear.EndpointMinimalPair
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.GroupTheory.CenterlessSubgroupPrimeCentralizer
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.GroupTheory.PCoreQuotientInnerJoin
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner

/-!
# Actual endpoint source parabolics for an inner binary-linear Sylow action

Transport both endpoint minimal parabolics through the original marking.
An inner action preserving S_L fixes both nodes, hence the full original S
normalizes their images. Their literal two-core quotients are S₃, whose
inner automorphism property identifies the quotient after adjoining N_S(L).
The characteristic-two clause comes from the actual proper Sylow overgroups.

Each two-residual contains at least sixteen elements. A central product
of actual A₃ blocks in a group with order prime to nine has order at most
twelve, since two distinct centerless A₄ factors would force two factors
of three. Thus neither endpoint residual is such a product. The same pair
generates L with M_L, giving every field of OrdinaryLinearParabolicGeometry
under the same e. This constructor uses no placement premise.

The application in Linear/Application uses the independent original
15.1.22(*) placement, whose final discharge stays with
qt-e-15122-pre-exclusion-catalogue. The graph-action source-family
construction and cubic Ru exclusion remain with this ordinary owner.
Source: Aschbacher--Smith 15.1.22(7), printed pp.1099--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem linear_embedded_center_centralizer
    {C : Type*} [Group C] (f : C →* G) (hf : Function.Injective f)
    (U : Subgroup C) (hU : U.map f = d.SL) :
    (centralizer ((center U).map U.subtype : Set C)).map f ≤
      centralizer ((center d.SL).map d.SL.subtype : Set G) := by
  rintro _ ⟨x,hx,rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨u,hu,heu⟩ := (show (z : G) ∈ U.map f from hU.symm ▸ z.property)
  have huc : (⟨u,hu⟩ : U) ∈ center U := by
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    apply hf
    change f ((v : C) * u) = f (u * (v : C))
    rw [map_mul,map_mul,heu]
    have hv : f v ∈ d.SL := hU ▸ mem_map_of_mem f v.property
    exact congrArg Subtype.val (mem_center_iff.mp hz (⟨f v,hv⟩ : d.SL))
  have hc := (mem_centralizer_iff.mp hx) u (mem_map_of_mem U.subtype huc)
  change (z : G) * f x = f x * z
  rw [←heu,←map_mul,←map_mul,hc]

/-- With only one factor of three in the ambient order, a product of A₃
blocks can contain at most one actual A₄ factor. -/
theorem aThreeProduct_residual_card_le (P : Subgroup G)
    (h9 : ¬ 9 ∣ Nat.card P) (h : IsAThreeProduct P) :
    Nat.card (pResidual 2 P) ≤ 12 := by
  classical
  obtain ⟨F,hF,hcomm,hgen⟩ := h
  have hcard (A : Subgroup P) (hA : A ∈ F) : Nat.card A = 12 := by
    obtain ⟨e⟩ := (hF A hA).2.equiv_alternatingFour
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hsub : F.Subsingleton := by
    intro A hA B hB
    by_contra hne
    have hc : B ≤ centralizer (A : Set P) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hcomm hA hB hne))
    obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hcard B hB]; decide)
    have he : orderOf (b : P) = 3 := by
      exact (orderOf_injective B.subtype B.subtype_injective b).trans hb
    exact no_prime_centralizer_of_square_free_order A (hF A hA).2.center_eq_bot
      (by rw [hcard A hA]; decide) h9 b (hc b.property) he
  rcases F.eq_empty_or_nonempty with he | ⟨A,hA⟩
  · rw [he,sSup_empty] at hgen
    rw [←hgen,card_bot]
    decide
  · have he : F = {A} := hsub.eq_singleton_of_mem hA
    rw [he,csSup_singleton] at hgen
    rw [←hgen,hcard A hA]

private theorem quotient_inner_of_symmetricThree {A : Type*} [Group A]
    (e : A ≃* Equiv.Perm (Fin 3)) :
    center A = ⊥ ∧ ∀ a : MulAut A, a ∈ MulAut.innerSubgroup A := by
  constructor
  · apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    apply NormalSymmetricThreePairRank.symmetricThree_center_trivial
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  · intro a
    obtain ⟨x,hx⟩ := NormalSymmetricThreePairRank.symmetricThree_aut_inner (MulAut.congr e a)
    have hi : MulAut.congr e a ∈ MulAut.innerSubgroup (Equiv.Perm (Fin 3)) := ⟨x,hx.symm⟩
    rw [←MulAut.map_innerSubgroup_congr e] at hi
    simpa only [MulEquiv.symm_apply_apply] using mem_map_equiv.mp hi

private theorem source_of_symmetricThree (s : d.PreExclusionSource h.normalized p)
    (P : Subgroup G) (hPL : P ≤ d.L) (hn : d.S ≤ normalizer (P : Set G))
    (hfit : generalizedFitting P = pCore 2 P)
    (e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (h9 : ¬9 ∣ Nat.card P) (hcard : 16 ≤ Nat.card (pResidual 2 P)) :
    d.IsSourceParabolic P := by
  have hq := quotient_inner_of_symmetricThree e
  refine ⟨hPL,inf_le_left.trans hn,hfit,.inl ⟨?_⟩,?_⟩
  · exact (pCoreJoinQuotientEquivOfInner P d.sylowNormalizer
      (inf_le_left.trans hn) ((Chapter1.isSylowIn_iff.mp s.centralizer_sylow).1.to_le inf_le_left)
      hq.1 (fun _ => hq.2 _)).trans e
  · intro hA
    have hh := aThreeProduct_residual_card_le P h9 hA
    omega

private theorem inner_embedded_invariant
    {C : Type*} [Group C] (e : d.L ≃* C) (P : Sylow 2 d.L)
    (hP : (P : Subgroup d.L).map d.L.subtype = d.SL)
    (X : Subgroup C)
    (hn : d.S ≤ normalizer (d.L : Set G))
    (hi : d.S ≤ d.L ⊔ centralizer (d.L : Set G))
    (hinv : ∀ a : MulAut C, a ∈ MulAut.innerSubgroup C →
      ((P : Subgroup d.L).map e.toMonoidHom).map a.toMonoidHom =
        (P : Subgroup d.L).map e.toMonoidHom → X.map a.toMonoidHom = X) :
    d.S ≤ normalizer (X.map (d.L.subtype.comp e.symm.toMonoidHom) : Set G) := by
  let f := d.L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := d.L.subtype_injective.comp e.symm.injective
  have hS : ((P : Subgroup d.L).map e.toMonoidHom).map f = d.SL := by
    rw [map_map]
    have he : f.comp e.toMonoidHom = d.L.subtype := by ext x; simp [f]
    rw [he,hP]
  intro x hx
  let a := d.L.normalizerMonoidHom ⟨x,hn hx⟩
  let b := MulAut.congr e a
  have ha : a ∈ MulAut.innerSubgroup d.L := by
    have hh := congrArg (fun U : Subgroup (normalizer (d.L : Set G)) =>
      (⟨x,hn hx⟩ : normalizer (d.L : Set G)) ∈ U) (normalizerMonoidHom_comap_conj_range d.L)
    exact (Eq.mp hh.symm (hi hx))
  have hb : b ∈ MulAut.innerSubgroup C :=
    MulAut.map_innerSubgroup_congr e ▸ mem_map_of_mem (MulAut.congr e).toMonoidHom ha
  have he : f.comp b.toMonoidHom = (MulAut.conj x).toMonoidHom.comp f := by
    ext y
    change (e.symm (e (a (e.symm y))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hSb : ((P : Subgroup d.L).map e.toMonoidHom).map b.toMonoidHom =
      (P : Subgroup d.L).map e.toMonoidHom := by
    apply map_injective hf
    rw [map_map,he,←map_map,hS]
    exact mem_normalizer_iff_map_conj_eq.mp
      (inf_normalizer_le_normalizer_inf ⟨d.S.le_normalizer hx,hn hx⟩)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (X.map f).map (MulAut.conj x).toMonoidHom = X.map f
  rw [map_map,←he,←map_map,hinv b hb hSb]

/-- Construct the literal generating source-parabolic family when S acts
innerly on the original binary-linear component. -/
theorem PreExclusionSource.binaryLinear_inner_parabolic_geometry
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : d.L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hi : d.S ≤ d.L ⊔ centralizer (d.L : Set G)) :
    Nonempty (d.OrdinaryLinearParabolicGeometry e) := by
  let a := e.trans (slEquivLinear n)
  let : Finite (LinearGroup n) := Finite.of_equiv d.L a.toEquiv
  obtain ⟨P,hP⟩ := s.component_sylow
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hex : ∃ A B : Subgroup (LinearGroup n),
      (Q : Subgroup _) ≤ A ∧ (Q : Subgroup _) ≤ B ∧ A ≠ ⊤ ∧ B ≠ ⊤ ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      16 ≤ Nat.card (pResidual 2 A) ∧ 16 ≤ Nat.card (pResidual 2 B) ∧
      ¬ 9 ∣ Nat.card A ∧ ¬ 9 ∣ Nat.card B ∧
      (∀ b : MulAut (LinearGroup n), b ∈ MulAut.innerSubgroup _ →
        (Q : Subgroup _).map b.toMonoidHom = Q →
        A.map b.toMonoidHom = A ∧ B.map b.toMonoidHom = B) ∧
      centralizer ((center (Q : Subgroup (LinearGroup n))).map
        (Q : Subgroup (LinearGroup n)).subtype : Set (LinearGroup n)) ⊔ (A ⊔ B) = ⊤ := by
    rcases hn with rfl | rfl <;> exact exists_endpoint_minimal_pair (by decide) Q
  obtain ⟨A,B,hQA,hQB,hA,hB,⟨eA⟩,⟨eB⟩,hcA,hcB,h9A,h9B,hinv,hgen⟩ := hex
  let f := d.L.subtype.comp a.symm.toMonoidHom
  have hf : Function.Injective f := d.L.subtype_injective.comp a.symm.injective
  have hr : f.range = d.L := by
    rw [MonoidHom.range_comp,a.symm.toMonoidHom.range_eq_top_of_surjective a.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hQ : (Q : Subgroup (LinearGroup n)).map f = d.SL := by
    change ((P : Subgroup d.L).map a.toMonoidHom).map f = _
    rw [map_map]
    have he : f.comp a.toMonoidHom = d.L.subtype := by ext x; simp [f]
    rw [he,hP]
  have hnL := d.S_le_G1.trans (s.binaryLinear_normal (h := h) hG hL hn e)
  have hsource (X : Subgroup (LinearGroup n)) (hQX : (Q : Subgroup _) ≤ X)
      (hX : X ≠ ⊤) (eqX : (X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3))
      (hcX : 16 ≤ Nat.card (pResidual 2 X)) (h9X : ¬ 9 ∣ Nat.card X)
      (hiX : ∀ b : MulAut (LinearGroup n), b ∈ MulAut.innerSubgroup _ →
        (Q : Subgroup _).map b.toMonoidHom = Q → X.map b.toMonoidHom = X) :
      d.IsSourceParabolic (X.map f) := by
    let ex := X.equivMapOfInjective f hf
    have hnX : d.S ≤ normalizer (X.map f : Set G) :=
      inner_embedded_invariant a P hP X hnL hi hiX
    have hfitX : generalizedFitting X = pCore 2 X := by
      rcases hn with rfl | rfl <;>
        exact proper_sylow_overgroup_generalizedFitting Q X hQX hX
    apply source_of_symmetricThree (h := h) s (X.map f) (hr ▸ map_le_range f _) hnX
    · rw [←map_generalizedFitting_equiv ex,←pCore_map_iso 2 ex,hfitX]
    · exact (QuotientGroup.congr _ _ ex (pCore_map_iso 2 ex)).symm.trans eqX
    · rwa [card_map_of_injective hf]
    · rw [←map_pResidual_of_surjective 2 ex.toMonoidHom ex.surjective,
        card_map_of_injective ex.injective]
      exact hcX
  have hsA := hsource A hQA hA eA hcA h9A (fun b hb hq => (hinv b hb hq).1)
  have hsB := hsource B hQB hB eB hcB h9B (fun b hb hq => (hinv b hb hq).2)
  have hc : (centralizer ((center (Q : Subgroup (LinearGroup n))).map
      (Q : Subgroup (LinearGroup n)).subtype : Set (LinearGroup n))).map f ≤ d.ML := by
    apply le_trans (le_inf (hr ▸ map_le_range f _)
      (linear_embedded_center_centralizer f hf Q hQ))
    exact s.linear_centralizer_le (h := h) hG hM hu hL hn e
  refine ⟨⟨{A.map f,B.map f},?_,?_,fun K hSK hK =>
    s.linear_flag_overgroup (h := h) (by omega) e K hSK hK⟩⟩
  · intro X hX
    rcases Set.mem_insert_iff.mp hX with rfl | hX
    · exact hsA
    · rw [Set.mem_singleton_iff] at hX
      subst X
      exact hsB
  · rw [sSup_insert,csSup_singleton]
    apply le_antisymm (sup_le inf_le_right (sup_le hsA.le_component hsB.le_component))
    have hh := congrArg (map f) hgen
    rw [Subgroup.map_sup,Subgroup.map_sup,←MonoidHom.range_eq_map,hr] at hh
    exact hh.ge.trans (sup_le (hc.trans le_sup_left) le_sup_right)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
