module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64Parameters
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import Theory.Representation.BinaryDoubledNaturalCentralizer
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.GroupTheory.SimpleSubgroupSmallIndex

/-!
# The partner action on the full original abelian core

Order64 identifies the full MS core itself with two equally marked natural
modules. The original opposite component acts through their solvable
centralizer of order six, so its perfectness kills this action. The core
here is the original subgroup of G, not a Frattini quotient or a selected
natural constituent.
-/

public noncomputable section
set_option maxHeartbeats 600000
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS

private theorem perfect_double_action_eq_one {B : Type*} [Group B] [Group.IsPerfect B]
    (τ : Representation (ZMod 2) B (BinaryDoubledNatural.Space 3))
    (hc : ∀ b g v, τ b (BinaryDoubledNatural.representation 3 g v) =
      BinaryDoubledNatural.representation 3 g (τ b v)) : τ = 1 := by
  let C := centralizer (BinaryDoubledNatural.component 3 :
    Set (BinaryDoubledNatural.Ambient 3))
  let f : B →* C := τ.asGroupHom.codRestrict C (by
    intro b
    apply mem_centralizer_iff.mpr
    rintro _ ⟨g,rfl⟩
    apply Units.ext
    exact LinearMap.ext (fun v => (hc b g v).symm))
  let : Finite C := Finite.of_equiv (Equiv.Perm (Fin 3))
    (BinaryDoubledNatural.centralizerEquiv (by decide : 2 ≤ 3)).toEquiv.symm
  let : Group.IsSolvable C := Group.isSolvable_of_card_le_six
    (le_of_eq (BinaryDoubledNatural.card_centralizer (by decide : 2 ≤ 3)))
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hz : f.range = ⊥ := by
    by_contra hne
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  apply MonoidHom.ext
  intro b
  have he : f b = 1 := mem_bot.mp (hz ▸ (show f b ∈ f.range from ⟨b,rfl⟩))
  exact congrArg (fun x : C => (x.val : Module.End (ZMod 2)
    (BinaryDoubledNatural.Space 3))) he

private theorem perfect_centralizes_double_section
    {G : Type*} [Group G] {L C B : Subgroup G} [IsElementaryAbelian 2 C]
    [Group.IsPerfect B]
    (α : L →* BinaryDoubledNatural.SL 3) (hα : Function.Surjective α)
    (d : BinaryConjugationSection L C ⊥
      ((BinaryDoubledNatural.representation 3).comp α))
    (hBC : B ≤ normalizer (C : Set G))
    (hcomm : ⁅B,L⁆ ≤ centralizer (C : Set G)) : B ≤ centralizer (C : Set G) := by
  obtain ⟨τ,hτ⟩ := d.exists_original_quotient_action hBC
    (show B ≤ normalizer (↑(⊥ : Subgroup G) : Set G) from le_normalizer_of_normal)
  have hco (b : B) (l : L) :
      Commute (C.normalizerMonoidHom (inclusion hBC b))
        (C.normalizerMonoidHom (inclusion d.normalized l)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    change ⁅inclusion hBC b,inclusion d.normalized l⁆ ∈ C.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hcomm (commutator_mem_commutator b.property l.property)
  have hτone : τ = 1 := perfect_double_action_eq_one τ (by
    intro b g v
    obtain ⟨l,rfl⟩ := hα g
    obtain ⟨c,hc⟩ := d.onto (Multiplicative.ofAdd v)
    have hv : (d.coordinates c).toAdd = v := congrArg Multiplicative.toAdd hc
    rw [←hv]
    change τ b (((BinaryDoubledNatural.representation 3).comp α) l
      (d.coordinates c).toAdd) =
      ((BinaryDoubledNatural.representation 3).comp α) l (τ b (d.coordinates c).toAdd)
    rw [←d.equivariant,hτ,hτ,←d.equivariant]
    exact congrArg (fun c : C => (d.coordinates c).toAdd)
      (DFunLike.congr_fun (hco b l).eq c))
  intro b hb c hc
  let b' : B := ⟨b,hb⟩
  let c' : C := ⟨c,hc⟩
  let c'' := C.normalizerMonoidHom (inclusion hBC b') c'
  have he : d.coordinates c'' = d.coordinates c' := by
    apply Multiplicative.toAdd.injective
    exact (hτ b' c').symm.trans (by rw [hτone]; rfl)
  have hz : c'' * c'⁻¹ = 1 := by
    apply Subtype.ext
    apply mem_bot.mp
    apply (d.coordinates_eq_one_iff _).mp
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hcfix : b*c*b⁻¹ = c := congrArg Subtype.val (mul_inv_eq_one.mp hz)
  exact (mul_inv_eq_iff_eq_mul.mp hcfix).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The opposite original component centralizes the complete abelian
MS core of order64, using the literal two-natural quotient coordinates. -/
theorem normalizerEscape_fullCore64_partner_structure
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let C := ⁅(localJoin T L).pCoreIn 2,L⁆
    IsElementaryAbelian 2 C ∧ C ⊓ centralizer (L : Set G) = ⊥ ∧
      L.map (MulAut.conj s.exchange).toMonoidHom ≤ centralizer (C : Set G) := by
  let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
  let A := L.subgroupOf J
  let C₀ := commutatorCore A
  let C := C₀.map J.subtype
  let B := L.map (MulAut.conj s.exchange).toMonoidHom
  let h := normalizerEscapeBinaryInput D (selected_nonnormal s) hout s.quotient
  let a : A ≃* L := subgroupOfEquivOfLe le_sup_left
  let c : C₀ ≃* C := C₀.equivMapOfInjective J.subtype J.subtype_injective
  have hCC : ⁅(localJoin T L).pCoreIn 2,L⁆ = C :=
    normalizerEscape_join_core_component D (selected_nonnormal s) hout s.quotient
  have hCcard : Nat.card C₀ = 64 := by
    change Nat.card C = 64 at hcard
    simpa only [C,card_map_of_injective J.subtype_injective] using hcard
  obtain ⟨m,hm,⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  have hm2 : m = 2 := by
    rcases hm with hm | hm
    · have hb := (h.abelianCore_fixedKernel_bounds hc (Or.inl hm) q).1
      have he := q.card
      rw [hm] at he
      change Nat.card C₀ = 2^(3*1) * Nat.card (coreFixed A) at he
      rw [hCcard] at he
      change Nat.card (coreFixed A) ≤ 2 at hb
      norm_num at he
      omega
    · exact hm
  subst m
  have hfixed : coreFixed A = ⊥ :=
    (eq_bot_iff_card _).mpr (h.abelianCore_fixedKernel_eq_one_of_twoCopies hc q)
  have hqin : Function.Injective q.projection :=
    (MonoidHom.ker_eq_bot_iff q.projection).mp (q.kernel.trans hfixed)
  let e := c.symm.trans (MulEquiv.ofBijective q.projection ⟨hqin,q.surjective⟩)
  let : IsElementaryAbelian 2 C₀ := h.abelianCore_elementary_of_naturalQuotient hc q
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map J.subtype
  let α : L →* BinaryDoubledNatural.SL 3 :=
    q.quotientEquiv.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 A)).comp a.symm.toMonoidHom)
  have hα : Function.Surjective α :=
    q.quotientEquiv.surjective.comp ((QuotientGroup.mk'_surjective _).comp a.symm.surjective)
  have hCL : C ≤ L := by
    have he : A.map J.subtype = L := map_subgroupOf_eq_of_le le_sup_left
    exact (map_mono (h.commutatorCore_le.trans (map_subtype_le _))).trans_eq he
  have hLC : L ≤ normalizer (C : Set G) := by
    rw [←hCC]
    exact normalizer_commutator_ge_right _ _
  let d : BinaryConjugationSection L C ⊥
      ((BinaryDoubledNatural.representation 3).comp α) := {
    section_le := hCL
    kernel_le := bot_le
    normalized := hLC
    coordinates := e.toMonoidHom
    onto := e.surjective
    kernel_eq := by
      rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
      ext x
      exact ⟨fun hx => congrArg Subtype.val (mem_bot.mp hx),
        fun hx => mem_bot.mpr (Subtype.ext hx)⟩
    equivariant := by
      intro l x
      funext i
      have he : c (h.coreConjugate (a.symm l) (c.symm x)) =
          (⟨(l:G)*x*(l:G)⁻¹,(mem_normalizer_iff.mp (hLC l.property) x).mp x.property⟩ : C) := by
        apply Subtype.ext
        have hv := congrArg J.subtype (h.coreConjugate_val (a.symm l) (c.symm x))
        have hx := congrArg Subtype.val (c.apply_symm_apply x)
        change ((c.symm x : J) : G) = (x:G) at hx
        change ((h.coreConjugate (a.symm l) (c.symm x) : J) : G) =
          (l:G)*((c.symm x : J) : G)*(l:G)⁻¹ at hv
        rw [hx] at hv
        exact hv
      change (q.projection (c.symm _)).toAdd i = _
      rw [←he,c.symm_apply_apply]
      exact q.equivariant (a.symm l) (c.symm x) i }
  have hBR : B ≤ localOrbit T L := by
    rintro _ ⟨l,hl,rfl⟩
    exact (originalConjugateOrbitInclusion
      s.exchange_mem ⟨l,hl⟩).property
  have hBL : B ≤ normalizer (L : Set G) :=
    hBR.trans (source_nonnormal_orbit_le_normalizer D (selected_nonnormal s))
  have hBC : B ≤ normalizer (C : Set G) := by
    rw [←hCC]
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator]
    rw [mem_normalizer_iff_map_conj_eq.mp (hBL hb)]
    have hbn : b ∈ normalizer ((localJoin T L).pCoreIn 2 : Set G) :=
      ((localJoin T L).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
          ((show localOrbit T L ≤ localJoin T L from le_sup_left) (hBR hb))
    rw [mem_normalizer_iff_map_conj_eq.mp hbn]
  let : Group.IsPerfect A := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map (MulAut.conj s.exchange).toMonoidHom
  have hcentral : L.pCoreIn 2 ≤ centralizer (C : Set G) := by
    intro n hn x hx
    obtain ⟨n,hn,rfl⟩ := hn
    obtain ⟨x,hx,rfl⟩ := hx
    have hna : a.symm n ∈ pCore 2 A := by
      have he := pCore_map_iso 2 a.symm
      rw [←he]
      exact mem_map_of_mem a.symm.toMonoidHom hn
    have hz := h.abelianCore_componentCore_centralizes_of_naturalQuotient hc q hx
      (a.symm n : J) (mem_map_of_mem A.subtype hna)
    exact (congrArg Subtype.val hz).symm
  have hcomm : ⁅B,L⁆ ≤ L.pCoreIn 2 := by
    have hrad : ⁅B,L⁆ ≤ (localJoin T L).pCoreIn 2 := by
      rw [commutator_comm]
      change ⁅L,B⁆ ≤ (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G)).pCoreIn 2
      rw [componentOrbit_sup]
      exact source_conjugate_commutator_le_core D.simpleQTKE D.maximal.1
        s.exchange_mem s.exchange_moves
    exact (le_inf (le_normalizer_iff_commutator_le_right.mp hBL) hrad).trans
      (inf_pCoreIn_le_of_le 2 ((le_componentOrbit L T).trans le_sup_left))
  have hCZ : C ⊓ centralizer (L : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    let x₀ := c.symm (⟨x,hx.1⟩ : C)
    have hv : ((x₀ : J) : G) = x :=
      congrArg Subtype.val (c.apply_symm_apply (⟨x,hx.1⟩ : C))
    have hz : x₀ ∈ coreFixed A := by
      intro l hl
      apply Subtype.ext
      change (l:G)*((x₀:J):G) = ((x₀:J):G)*(l:G)
      rw [hv]
      exact hx.2 l hl
    have hx₀ : x₀ = 1 := mem_bot.mp (hfixed ▸ hz)
    have he := congrArg (fun y : C₀ => ((y:J):G)) hx₀
    rw [hv] at he
    exact he
  dsimp only
  rw [hCC]
  exact ⟨inferInstance,hCZ,
    perfect_centralizes_double_section α hα d hBC (hcomm.trans hcentral)⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
