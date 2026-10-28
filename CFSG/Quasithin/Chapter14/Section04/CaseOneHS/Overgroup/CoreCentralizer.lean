module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Normalizers
public import Theory.Representation.FirstCohomologyAutomorphism.FixedElement
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinaryInvolution

/-!
# The original Sylow centralizers in the HS branch

An element centralizing PU has its L-displacements in the abelian P.
Squaring puts these displacements in V. The natural binary SL₃ cohomology
calculation detects a principal cocycle on an actual involution coming
from U; C_T(L)=1 then puts the squared element in V₁. Adjusting by a square
root in the original cyclic Z(U) gives an involution. Applying the same
calculation again proves C_T(PU)=Z(U), hence C_T(U)=C_T(K)=Z(U).

This supplies the source's automorphism-centralizer argument without
assuming an abstract identification of the whole extension L.
Source: Aschbacher--Smith, proof of 14.3.33, printed p.1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- An actor fixing PU and with all L-displacements in V belongs to the
original point. The fixed nontrivial quotient involution excludes the
exceptional natural cocycle. -/
theorem core_closure_centralizer_mem_point_of_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hxT : x ∈ T) (hxC : x ∈ centralizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G))
    (hdis : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ V) : x ∈ F.Vi 1 := by
  let := h.chosen.elementary
  let e := h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let a := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : a.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let c : V ≃* Multiplicative (Fin 3 → ZMod 2) :=
    h.naturalMarking.coordinates.toAddEquiv.toMultiplicativeRight
  let N := V.subgroupOf L
  let eN : N ≃* Multiplicative (Fin 3 → ZMod 2) :=
    (subgroupOfEquivOfLe h.chosen.le_component).trans c
  let ρ := Representation.specialLinearNatural (k := ZMod 2) 3
  have heN (g : L) (w : Fin 3 → ZMod 2) :
      (eN.symm (Multiplicative.ofAdd (ρ (a g) w)) : L) =
        g * (eN.symm (Multiplicative.ofAdd w) : L) * g⁻¹ := by
    apply Subtype.ext
    change (c.symm (Multiplicative.ofAdd (ρ (a g) w)) : G) =
      (g : G) * (c.symm (Multiplicative.ofAdd w) : G) * (g : G)⁻¹
    have hv := h.naturalMarking.equivariant g (Additive.ofMul (c.symm (Multiplicative.ofAdd w)))
    have he := congrArg (fun b : BinaryLinear.OuterCyclic.LinearGroup 3 => b w)
      ((BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply
        (h.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) g)))
    have hv' : c (setupSeedAction L V h.chosen.normalizes g (c.symm (Multiplicative.ofAdd w))) =
        Multiplicative.ofAdd (ρ (a g) w) := by
      apply Multiplicative.toAdd.injective
      have hcw : h.naturalMarking.coordinates
          (Additive.ofMul (c.symm (Multiplicative.ofAdd w))) = w :=
        congrArg Multiplicative.toAdd (c.apply_symm_apply _)
      rw [hcw] at hv
      exact hv.trans he.symm
    exact congrArg Subtype.val ((c.symm_apply_eq.mpr hv'.symm))
  have hnot : ¬ F.U ≤ L.pCoreIn 2 := by
    intro hu
    have hi := centerSpan_inf_closure_card h structural alternatives F s hne
    rw [centerSpan_eq_core h structural alternatives F s hne, inf_eq_right.mpr hu,
      s.core_shape.card] at hi
    omega
  obtain ⟨u, hu, hun⟩ := SetLike.not_le_iff_exists.mp hnot
  let l : L := ⟨u, closure_le_actor h structural alternatives F s hne hu⟩
  have hl1 : a l ≠ 1 := by
    intro he
    exact hun (mem_map_of_mem L.subtype (hk ▸ (show l ∈ a.ker from he)))
  have hl2 : a l * a l = 1 := by
    rw [← map_mul]
    apply MonoidHom.mem_ker.mp
    rw [hk]
    have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L
      (normalizer (L : Set G)) (by decide) h.chosen.le_sylow h.chosen.normalizes
      (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
      (h.flag_escape_at F alternatives) hne
    let : Fact (IsPGroup 2 F.U) := ⟨IsPGroup.of_card (n := 6) s.core_shape.card⟩
    have hs := pth_power_mem_frattini_of_isPGroup (p := 2) (⟨u, hu⟩ : F.U)
    have hu2 : u * u ∈ F.Vi 1 := by
      rw [hphi] at hs
      change u ^ 2 ∈ F.Vi 1 at hs
      simpa only [pow_two] using hs
    have hP := (seed_le_centerSpan h F).trans
      (centerSpan_eq_core h structural alternatives F s hne).le (F.le_seed 1 hu2)
    obtain ⟨y, hy, he⟩ := hP
    exact (Subtype.ext he : y = l * l) ▸ hy
  let α : MulAut L := L.normalizerMonoidHom ⟨x, h.sylow_normalizes_at structural hxT⟩
  have hfix (n : L) (hn : n ∈ a.ker) : α n = n := by
    apply Subtype.ext
    have hnP := mem_map_of_mem L.subtype (hk ▸ hn)
    change x * (n : G) * x⁻¹ = n
    rw [← hxC n (mem_sup_left hnP), mul_inv_cancel_right]
  have hfixed : α l = l := by
    apply Subtype.ext
    change x * u * x⁻¹ = u
    rw [← hxC u (mem_sup_right hu), mul_inv_cancel_right]
  obtain ⟨v, hv⟩ := Representation.OneCohomology.automorphism_inner_of_fixed_element_of_subkernel
    N a ha eN ρ heN l (fun z hz =>
      Representation.OneCohomology.SLHigherNatural.SLThreeBinary.principal_of_zero_involution
        z (a l) hl1 hl2 hz) α (fun g => hdis g g.property) hfix hfixed
  have hvV : ((v : L) : G) ∈ V := v.property
  have hzero : ((v : L) : G) * x = 1 := by
    apply mem_bot.mp
    rw [← sylow_actor_centralizer_eq_bot h structural alternatives F s hne]
    refine ⟨(T : Subgroup G).mul_mem (h.chosen.le_sylow hvV) hxT, ?_⟩
    intro g hg
    have he := congrArg Subtype.val (hv ⟨g, hg⟩)
    change x * g * x⁻¹ = ((v : L) : G)⁻¹ * g * (v : L) at he
    calc
      g * (((v : L) : G) * x) = ((v : L) : G) *
          (((v : L) : G)⁻¹ * g * (v : L)) * x := by group
      _ = ((v : L) : G) * (x * g * x⁻¹) * x := by rw [he]
      _ = (((v : L) : G) * x) * g := by group
  have hxV : x ∈ V := (eq_inv_of_mul_eq_one_right hzero).symm ▸ V.inv_mem hvV
  have hxZ : x ∈ F.ZU := by
    rw [ZU, centerIn_eq_inf_centralizer]
    exact ⟨le_conjugateSpanBy V F.H hxV, centralizer_le (show F.U ≤ L.pCoreIn 2 ⊔ F.U from le_sup_right) hxC⟩
  let := F.localKernel_tilde_seed_elementary
  rw [← F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne]
  exact ⟨hxV, hxZ⟩

omit [Finite G] in
private theorem commutator_square_of_commute (x l : G) (hc : Commute x ⁅x, l⁆) :
    ⁅x ^ 2, l⁆ = ⁅x, l⁆ ^ 2 := by
  calc
    ⁅x ^ 2, l⁆ = x * ⁅x, l⁆ * x⁻¹ * ⁅x, l⁆ := by
      simp only [commutatorElement_def, pow_two]
      group
    _ = ⁅x, l⁆ ^ 2 := by rw [hc.eq, mul_inv_cancel_right, pow_two]

/-- Fixing PU makes every displacement on L lie in its actual abelian core. -/
theorem core_closure_centralizer_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hxT : x ∈ T) (hxC : x ∈ centralizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G))
    (l : G) (hl : l ∈ L) : ⁅x, l⁆ ∈ L.pCoreIn 2 := by
  have hVP : V ≤ L.pCoreIn 2 := (seed_le_centerSpan h F).trans
    (centerSpan_eq_core h structural alternatives F s hne).le
  have hxV := centralizer_le (hVP.trans le_sup_left) hxC
  have hc : ⁅x, l⁆ ∈ centralizer (V : Set G) := by
    have hn := (normalizer_le_normalizer_centralizer V) (h.chosen.normalizes hl)
    have hh := (centralizer (V : Set G)).mul_mem hxV
      ((mem_normalizer_iff.mp hn x⁻¹).mp ((centralizer _).inv_mem hxV))
    simpa only [commutatorElement_def, mul_assoc] using hh
  have hL : ⁅x, l⁆ ∈ L := L.mul_mem
    ((mem_normalizer_iff.mp (h.sylow_normalizes_at structural hxT) l).mp hl) (L.inv_mem hl)
  exact h.centralizer_L ▸ ⟨hL, hc⟩

/-- The actual Sylow centralizer of O₂(L₁)=PU is exactly Z(U). -/
theorem sylow_core_closure_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    (T : Subgroup G) ⊓ centralizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G) = F.ZU := by
  let := h.chosen.elementary
  let := centerSpan_abelian h structural F s
  have heP := centerSpan_eq_core h structural alternatives F s hne
  have hZP : F.ZU ≤ L.pCoreIn 2 := (le_conjugateSpanBy F.ZU L).trans heP.le
  have hZT : F.ZU ≤ (T : Subgroup G) :=
    (map_subtype_le (center F.U)).trans (closure_le_sylow F s)
  have hZC : F.ZU ≤ centralizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mp
    refine sup_le ?_ (le_centralizer_iff.mp (centerIn_le_centralizer F.U))
    intro p hp z hz
    exact congrArg Subtype.val (mul_comm (⟨z, le_conjugateSpanBy F.ZU L hz⟩ : centerSpan L F)
      ⟨p, heP.symm ▸ hp⟩)
  apply le_antisymm ?_ (le_inf hZT hZC)
  rintro x ⟨hxT, hxC⟩
  have hx2 : x ^ 2 ∈ F.Vi 1 := by
    apply core_closure_centralizer_mem_point_of_displacement h structural alternatives F s hne
      (x ^ 2) ((T : Subgroup G).pow_mem hxT 2) ((centralizer _).pow_mem hxC 2)
    intro l hl
    have hd := core_closure_centralizer_displacement h structural alternatives F s hne x hxT hxC l hl
    have hc : Commute x ⁅x, l⁆ := (hxC _ (mem_sup_left hd)).symm
    change ⁅x ^ 2, l⁆ ∈ V
    rw [commutator_square_of_commute x l hc]
    exact centerSpan_square_mem_seed h structural F s (heP.symm ▸ hd)
  have hsq : x ^ 2 ∈ (centralSquares F.U).map F.U.subtype :=
    (center_squares_eq_point h F s).symm ▸ hx2
  obtain ⟨u, hu, he⟩ := hsq
  obtain ⟨z, hz⟩ := mem_centralSquares.mp hu
  let zG : G := z.val
  have hzZ : zG ∈ F.ZU := mem_map_of_mem F.U.subtype z.property
  have hz2 : zG ^ 2 = x ^ 2 := (congrArg Subtype.val hz).trans he
  let y := zG⁻¹ * x
  have hyT : y ∈ T := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hZT hzZ)) hxT
  have hyC : y ∈ centralizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G) :=
    (centralizer _).mul_mem ((centralizer _).inv_mem (hZC hzZ)) hxC
  have hy2 : y ^ 2 = 1 := by
    have hc : Commute zG x := hxC zG (mem_sup_left (hZP hzZ))
    dsimp only [y]
    rw [hc.inv_left.mul_pow, inv_pow, hz2, inv_mul_cancel]
  have hy : y ∈ F.Vi 1 := by
    apply core_closure_centralizer_mem_point_of_displacement h structural alternatives F s hne y hyT hyC
    intro l hl
    have hd := core_closure_centralizer_displacement h structural alternatives F s hne y hyT hyC l hl
    have hc : Commute y ⁅y, l⁆ := (hyC _ (mem_sup_left hd)).symm
    have hs : ⁅y, l⁆ ^ 2 = 1 := by rw [← commutator_square_of_commute y l hc, hy2]; simp
    exact (centerSpan_square_kernel_and_card h structural alternatives F s hne).1 _
      (heP.symm ▸ hd) |>.mp hs
  have hh := F.ZU.mul_mem hzZ (F.point_le_ZU (by decide) hy)
  simpa only [y, mul_inv_cancel_left] using hh

/-- The point core and original component have precisely the same Sylow
centralizer, namely the original cyclic Z(U). -/
theorem sylow_closure_and_component_centralizers
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    (T : Subgroup G) ⊓ centralizer (F.U : Set G) = F.ZU ∧
      (T : Subgroup G) ⊓ centralizer (K : Set G) = F.ZU := by
  let := h.chosen.elementary
  have he := sylow_centralizer_closure_eq_component h structural alternatives F s hne K hKH hK hKT hU
  have hKZ : (T : Subgroup G) ⊓ centralizer (K : Set G) ≤ F.ZU := by
    rw [← sylow_core_closure_centralizer h structural alternatives F s hne]
    exact inf_le_inf_left _ (centralizer_le
      (core_closure_le_component h structural alternatives F s hne K hKH hK hKT hU))
  have hZU : F.ZU ≤ (T : Subgroup G) ⊓ centralizer (F.U : Set G) :=
    le_inf ((map_subtype_le (center F.U)).trans (closure_le_sylow F s)) (centerIn_le_centralizer F.U)
  have hUe := le_antisymm (he.le.trans hKZ) hZU
  exact ⟨hUe, he.symm.trans hUe⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
