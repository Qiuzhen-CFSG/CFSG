module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuNearOffenders.Certificate
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeAvoidance
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction

/-!
# M24 cocode near-offenders and escaping subspaces

The existing displacement bound forces a near-offender to have order at least
sixteen. Rank-nullity gives the product bound used by the checked native Sylow
certificate. Thus every near-offender conjugates into the actual octad kernel.
Its noncyclic fixed space is the octad six-space, where pair avoidance bounds
subspaces by three. Transport through the original automizer marking supplies
both local-action premises of E.6.27.

The chosen-orbit consumer is NonFFSourceMathieuM24Bounds. It keeps the preceding
8.1.1 ambient pair-centralizer containment explicit; its proof and final J4
assembly remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith H.15.2(1,3,5) and 8.1.2, pp.398--399,713.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open MathieuCode MathieuCode.CocodeOctad.Involutions
open CFSG.Quasithin.ChapterH.Section13To16
open CFSG.Quasithin.Chapter7.NormalizedSource.MathieuNearOffenderCertificate
open SylowNormalizer.OrderEnumeration SylowCoverage
open scoped BigOperators IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuAvoidance
open ChapterE
private theorem allowed_points : ∀ v : Fin 192, v ∈ allowed →
    ∀ i : Fin 24, i ∈ standardOctad.val →
      transportPerm (vertexPoint v (transportPerm.symm i)) = i := by
  decide +kernel

private theorem allowed_kernel (v : Fin 192) (hv : v ∈ allowed) :
    transport * (native v).val * transport⁻¹ ∈
      (pCore 2 (octadStabilizer standardOctad)).map (octadStabilizer standardOctad).subtype := by
  rw [octad_core_map_eq_pointwise]
  apply (mem_octadPointwiseKernel standardOctad _).mpr
  intro i hi
  change transportPerm ((native v).val.val (transportPerm.symm i)) = i
  rw [native_apply]
  exact allowed_points v hv i hi

open scoped IsMulCommutative

theorem native_near_containment
    (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hA : A ≤ SylowNormalizer.candidate) (hcard : 16 ≤ Nat.card A)
    (hprod : 1024 ≤ Nat.card A * Nat.card (fixedSpace cocodeRepresentation A)) :
    A.map (MulAut.conj transport).toMonoidHom ≤
      (pCore 2 (octadStabilizer standardOctad)).map (octadStabilizer standardOctad).subtype := by
  classical
  let s : Finset (Fin 192) := Finset.univ.filter (fun v => (native v).val ∈ A)
  have hs (v : Fin 192) : v ∈ s ↔ (native v).val ∈ A := by simp [s]
  have cover (g : A) : ∃ v, (native v).val = g.val := by
    have hg : (⟨g.val,hA g.property⟩ : SylowNormalizer.candidate)^2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian g.val g.property
    obtain ⟨v,hv⟩ := vertex_of_square _ hg
    exact ⟨v,congrArg Subtype.val hv⟩
  let f : s → A := fun v => ⟨(native v.val).val,(hs v.val).mp v.property⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨v,hv⟩ := cover g
    exact ⟨⟨v,(hs v).mpr (hv.symm ▸ g.property)⟩,Subtype.ext hv⟩
  have hcs : Nat.card A ≤ s.card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
      Nat.card_le_card_of_surjective f hf
  let F : Finset (Fin 2048) := Finset.univ.filter (fun x =>
    ∃ z : fixedSpace cocodeRepresentation A, code z = x)
  have hCF : Nat.card (fixedSpace cocodeRepresentation A) ≤ F.card := by
    let f : fixedSpace cocodeRepresentation A → F := fun z => ⟨code z,by simp [F]⟩
    have hf : Function.Injective f := fun x y he => Subtype.ext
      (code_injective (congrArg Subtype.val he))
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hf
  have bound := check_sound certificate _ _ certificate_checked s F
    (fun v _ => List.mem_finRange v) (fun x _ => List.mem_finRange x)
    (hcard.trans hcs) (hprod.trans (Nat.mul_le_mul hcs hCF)) (by
      intro v hv w hw
      have he : (native v).val * (native w).val = (native w).val * (native v).val :=
        congrArg (fun a : A => a.val) (mul_comm
          (⟨(native v).val,(hs v).mp hv⟩ : A) (⟨(native w).val,(hs w).mp hw⟩ : A))
      exact native_compatible v w (Subtype.ext he)) (by
      intro v hv x hx
      obtain ⟨z,rfl⟩ : ∃ z : fixedSpace cocodeRepresentation A, code z = x := by
        simpa [F] using hx
      exact native_fixed_test v z (z.property ⟨(native v).val,(hs v).mp hv⟩))
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨v,hv⟩ := cover ⟨a,ha⟩
  have hb := allowed_kernel v (bound v ((hs v).mpr (hv.symm ▸ ha)))
  change transport * a * transport⁻¹ ∈ _
  simpa only [hv] using hb
open CFSG.Quasithin.Chapter7.NormalizedSource
open CFSG.Quasithin.ChapterH.Section13To16

theorem near_card_bounds (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hn : fixedCodim cocodeRepresentation A ≤ rank A + 1) :
    16 ≤ Nat.card A ∧ 1024 ≤ Nat.card A * Nat.card (fixedSpace cocodeRepresentation A) := by
  let := hA.2
  have hlow := largeMathieu_nearOffender_fixedCodim_ge_five cocodeRepresentation
    (Or.inr (Or.inr ⟨MulEquiv.refl _,Or.inl ⟨Representation.Equiv.refl _⟩⟩)) A hA hn
  have hcard : Nat.card A = 2 ^ rank A := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [rank,hn,Nat.log_pow Nat.one_lt_two]
  constructor
  · rw [hcard]
    exact Nat.pow_le_pow_right (n := 2) (i := 4) (by decide) (by omega)
  · rw [hcard,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←Nat.pow_add]
    have hd := fixedCodim_add_finrank cocodeRepresentation A
    rw [finrank_cocode] at hd
    exact Nat.pow_le_pow_right (n := 2) (i := 10) (by decide) (by omega)

noncomputable def conjugationEquiv (g : M24) : Cocode ≃ₗ[ZMod 2] Cocode :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom g)

theorem conjugation_equivariant (g a : M24) (v : Cocode) :
    conjugationEquiv g (cocodeRepresentation a v) =
      cocodeRepresentation ((MulAut.conj g).toMonoidHom a) (conjugationEquiv g v) := by
  change cocodeRepresentation g (cocodeRepresentation a v) =
    cocodeRepresentation (g*a*g⁻¹) (cocodeRepresentation g v)
  simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]

theorem conjugation_near (g : M24) (A : Subgroup M24)
    (hn : fixedCodim cocodeRepresentation A ≤ rank A + 1) :
    fixedCodim cocodeRepresentation (A.map (MulAut.conj g).toMonoidHom) ≤
      rank (A.map (MulAut.conj g).toMonoidHom) + 1 := by
  rw [rank_map_injective _ (MulAut.conj g).injective,
    ←fixedCodim_map_equivariant cocodeRepresentation cocodeRepresentation
      (MulAut.conj g).toMonoidHom (conjugationEquiv g) (conjugation_equivariant g)]
  exact hn

theorem m24_nearOffender_conjugate_octad
    (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hn : fixedCodim cocodeRepresentation A ≤ rank A + 1) :
    ∃ g : M24, A.map (MulAut.conj g).toMonoidHom ≤ octadKernel standardOctad := by
  let := hA.2
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : IsElementaryTwo B :=
    ⟨fun hb => hA.1 ((A.map_eq_bot_iff_of_injective (MulAut.conj g).injective).mp hb),inferInstance⟩
  have hBS : B ≤ SylowNormalizer.candidate := by
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAS
    change B ≤ (g • S : Sylow 2 M24) at h
    rw [hg] at h
    exact h
  obtain ⟨hc,hp⟩ := near_card_bounds B hB (conjugation_near g A hn)
  have hb  := native_near_containment B hBS hc hp
  refine ⟨transport*g,?_⟩
  have he : (MulAut.conj transport).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (transport*g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  change (A.map _).map _ ≤ _ at hb
  rw [Subgroup.map_map,he] at hb
  exact hb

/-- The source near-offender is the entire intrinsic octad kernel. The
order bound rules out proper subgroups after the checked conjugation. -/
theorem m24_nearOffender_conjugate_eq_octad
    (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hn : fixedCodim cocodeRepresentation A ≤ rank A + 1) :
    ∃ g : M24, A.map (MulAut.conj g).toMonoidHom = octadKernel standardOctad := by
  obtain ⟨g,hg⟩ := m24_nearOffender_conjugate_octad A hA hn
  refine ⟨g,Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  change Nat.card (M24ChapterHStabilizers.OctadAction.AmbientCore standardOctad) ≤ Nat.card A
  rw [M24ChapterHStabilizers.OctadAction.ambientCore_card]
  exact (near_card_bounds A hA hn).1

theorem m24_nearOffender_avoiding_rank
    (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hn : fixedCodim cocodeRepresentation A ≤ rank A + 1)
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace cocodeRepresentation A)
    (ha : Disjoint (I : Set Cocode) weightTwoOrbit) : Module.finrank (ZMod 2) I ≤ 3 := by
  let := hA.2
  obtain ⟨g,hg⟩ := m24_nearOffender_conjugate_eq_octad A hA hn
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hcard : 16 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact (near_card_bounds A hA hn).1
  have hnc : ¬ IsCyclic B := by
    intro hc
    let := hc
    obtain ⟨b,hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := B)
    have hd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 B) b)
    rw [hb] at hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  let J := I.map (conjugationEquiv g).toLinearMap
  have hJ : J ≤ fixedSpace cocodeRepresentation B := by
    rw [←fixedSpace_map_equivariant cocodeRepresentation cocodeRepresentation
      (MulAut.conj g).toMonoidHom (conjugationEquiv g) (conjugation_equivariant g)]
    exact Submodule.map_mono hI
  have haJ : Disjoint (J : Set Cocode) weightTwoOrbit := by
    apply Set.disjoint_left.mpr
    rintro z ⟨w,hw,rfl⟩ ⟨P,hP⟩
    apply Set.disjoint_left.mp ha hw
    refine ⟨mapPair g⁻¹ P,?_⟩
    rw [←pairVector_equivariant,hP]
    change cocodeRepresentation g⁻¹ (cocodeRepresentation g w) = w
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  rw [CocodeLocal.octad_noncyclic_fixedSpace standardOctad B hg.le hnc] at hJ
  have hb := CocodeLocal.octad_fixedSpace_avoiding_finrank_le standardOctad J hJ haJ
  rw [(conjugationEquiv g).finrank_map_eq] at hb
  exact hb


variable {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) [IsElementaryAbelian 2 W]

/-- Both literal local-action premises of E.6.27, with the near-offender
and odd-prime estimates proved on the full M24 cocode. -/
theorem m24_local_action_bounds (A U : Subgroup G)
    (hWA : W ≤ A) (hAN : A ≤ normalizer (W : Set G))
    (hUW : U ≤ W) (hAU : A ≤ centralizer (U : Set G))
    (a : Automizer W ≃* M24) (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) =
      cocodeRepresentation (a b) (E v))
    (ha : Disjoint (markedSpace W U E : Set Cocode) weightTwoOrbit)
    (hr : 3 < rank U) :
    ChapterE.Section06.FixedPointBounds.nPrime (inducedAutomizer W A) ≤ 1 ∧
      ChapterB.thompsonJ A 1 ≤ centralizer (W : Set G) := by
  have hdim := markedSpace_finrank W U hUW E
  constructor
  · apply nPrime_le_one_of_no_odd_prime
    intro p hp ho b hb
    let B := zpowers (b.val : Automizer W)
    have hfix := markedSpace_le_fixed W A U hAN hAU cocodeRepresentation
      a.toMonoidHom E hE B (zpowers_le.mpr b.property)
    have hc : Nat.card (B.map a.toMonoidHom) = p := by
      rw [card_map_of_injective a.injective,Nat.card_zpowers]
      simpa using hb
    have hd := m24_odd_avoiding_rank (B.map a.toMonoidHom) hp ho hc _ hfix ha
    omega
  · apply sSup_le
    intro B hB
    by_contra hn
    let := hB.2.1
    have hBN := hB.1.trans hAN
    let I := inducedAutomizer W B
    have hI : IsElementaryTwo I :=
      ⟨fun hb => hn ((inducedAutomizer_eq_bot_iff hBN).mp hb),
        inducedAutomizer_elementary W B hBN⟩
    have hIm : IsElementaryTwo (I.map a.toMonoidHom) := by
      let := hI.2
      exact ⟨fun hb => hI.1 ((I.map_eq_bot_iff_of_injective a.injective).mp hb),
        IsElementaryAbelian.map a.toMonoidHom⟩
    have hnear := thompson_family_fixedCodim_le W A hWA hAN B hB
    rw [fixedCodim_map_equivariant (automizerRepresentation W) cocodeRepresentation
      a.toMonoidHom E hE,←rank_map_injective a.toMonoidHom a.injective] at hnear
    have hfix := markedSpace_le_fixed W B U hBN (hB.1.trans hAU)
      cocodeRepresentation a.toMonoidHom E hE I le_rfl
    have hd := m24_nearOffender_avoiding_rank _ hIm hnear _ hfix ha
    omega


end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuAvoidance
