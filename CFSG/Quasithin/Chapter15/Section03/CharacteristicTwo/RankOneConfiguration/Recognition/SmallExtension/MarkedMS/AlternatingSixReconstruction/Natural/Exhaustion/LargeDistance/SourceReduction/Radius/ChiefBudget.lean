module
public import Theory.GroupAction.SymmetricSixChiefBudget.Quotient
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# The A₆ chief budget for the source radius

The original replacement maps onto A₆ with a two-group kernel. Each
noncentral binary chief factor has fixed index at least four under an
actor whose image contains an involution. Thus fixed index at most eight
allows at most one noncentral chief factor, even when the radius itself
is nonabelian. The quotient form retains the literal kernel, two-residual,
commutators and centralizer modulo the chosen normal subgroup.

The proof adapts the finite S₆ chief budget to its derived actor, reusing
its group-independent section-index inequality. The application is in
KernelCentrality in this directory. Source: MS93 (3.8), printed p.878.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open NoncentralChiefRefinement NoncentralChiefRefinement.SymmetricSixBudget
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.AlternatingBudget
variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem simple_fixedCodim_lower (q : H →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ] (hne : ρ ≠ 1)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q) :
    2 ≤ fixedCodim ρ A := by
  have hk : q.ker ≤ ρ.ker := normal_p_subgroup_le_ker ρ q.ker hp
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let σ := (quotientOfLEKer ρ q.ker hk).comp e.symm.toMonoidHom
  have he (h : H) : σ (q h) = ρ h := by
    change quotientOfLEKer ρ q.ker hk (e.symm (q h)) = _
    have hh : e.symm (q h) = QuotientGroup.mk' q.ker h := e.symm_apply_eq.mpr rfl
    rw [hh]
    rfl
  have hcomp : σ.comp q = ρ := MonoidHom.ext he
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q hq σ).mp
    (hcomp ▸ (inferInstance : IsIrreducible ρ))
  have hnσ : σ ≠ 1 := by
    intro hs
    apply hne
    rw [← hcomp, hs]
    rfl
  have hlow := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_involution_mem
    σ (by contrapose! hnσ; exact MonoidHom.ext hnσ) a ha haA
  have hfixed : fixedSpace ρ A = fixedSpace σ (A.map q) := by
    ext v
    constructor
    · intro hv g
      obtain ⟨x,hx,hxg⟩ := g.property
      change σ g.val v = v
      rw [← hxg, he]
      exact hv ⟨x,hx⟩
    · intro hv g
      have ht := hv ⟨q g, mem_map_of_mem q g.property⟩
      change σ (q g) v = v at ht
      rwa [he] at ht
  change 2 ≤ Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ A)
  rw [hfixed]
  exact hlow

section GroupModule
variable {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    [MulDistribMulAction H W] [Nontrivial W]

theorem simple_group_fixedIndex_lower (q : H →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (hirr : ∀ D : Subgroup W, (∀ h : H, ∀ w : W, w ∈ D → h • w ∈ D) →
      D = ⊥ ∨ D = ⊤)
    (hne : ¬ ∀ h : H, ∀ w : W, h • w = w) : 4 ≤ (FixedPoints.subgroup A W).index := by
  classical
  let ρ := Representation.ofElementaryAbelianAction (A := H) (G := W) (p := 2)
  let : IsIrreducible ρ := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, ?_⟩
    intro U
    let D : Subgroup W := AddSubgroup.toSubgroup' U.toSubmodule.toAddSubgroup
    rcases hirr D (fun h w hw => U.apply_mem_toSubmodule h hw) with hd | hd
    · left
      apply bot_unique
      intro v hv
      have hh : v.toMul ∈ D := hv
      rw [hd, Subgroup.mem_bot] at hh
      exact hh
    · right
      apply top_unique
      intro v _
      have hv : v.toMul ∈ D := by rw [hd]; trivial
      exact hv
  have hnρ : ρ ≠ 1 := by
    intro he
    apply hne
    intro h w
    exact congrArg (fun τ : Representation (ZMod 2) H (Additive W) => τ h (Additive.ofMul w)) he
  have hl := simple_fixedCodim_lower q hq hp ρ hnρ A a ha haA
  have hf : fixedSpace (ρ.comp A.subtype) ⊤ = fixedSpace ρ A := by
    ext v
    constructor
    · intro hv g
      exact hv ⟨g, mem_top g⟩
    · intro hv g
      exact hv g.val
  have hc := fixed_subgroup_index (ρ.comp A.subtype)
  rw [fixedCodim, hf] at hc
  have hg : AddSubgroup.toSubgroup' (fixedSpace ρ A).toAddSubgroup =
      FixedPoints.subgroup A W := by
    ext w
    rfl
  rw [hg] at hc
  rw [hc]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl
end GroupModule

/-- An index-eight actor above an involution of A₆ permits at most one
noncentral chief factor in an arbitrary normal two-subgroup. -/
theorem noncentralCount_le_one (q : H →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : IsPGroup 2 U)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (s : SeriesOn U) : s.noncentralCount ≤ 1 := by
  apply count_le_one_of_index s A _ hindex
  intro i hi
  let := s.factor_elementary hU i
  let := s.factor_nontrivial i
  let μ : MulDistribMulAction H (s.Factor i) := MulDistribMulAction.compHom _ (s.action i)
  let := μ
  exact simple_group_fixedIndex_lower q hq hp A a ha haA
    (s.factor_irreducible i) (fun ht => hi ((s.central_iff_action i).mpr ht))

/-- The source form: the original normal subgroup lies in the literal
normal two-kernel of the A₆ projection. No elementary-abelian premise occurs. -/
theorem noncentralCount_le_one_of_le_ker (q : H →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (s : SeriesOn U) : s.noncentralCount ≤ 1 :=
  noncentralCount_le_one q hq hp U
    (hp.of_injective (inclusion hU) (inclusion_injective hU)) A a ha haA hindex s

/-- The chief-series alternative used in the source: either every factor is
central, or one and only one actual factor is noncentral. -/
theorem central_or_unique_noncentral (q : H →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : IsPGroup 2 U)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (s : SeriesOn U) : (∀ i, s.Central i) ∨ (∃! i, ¬s.Central i) := by
  have h := noncentralCount_le_one q hq hp U hU A a ha haA hindex s
  rcases Nat.eq_zero_or_pos s.noncentralCount with hz | hz
  · exact Or.inl (s.noncentralCount_eq_zero_iff.mp hz)
  · exact Or.inr (s.noncentralCount_eq_one_iff.mp (by omega))


private theorem residual_dichotomy
    (q : H →* alternatingGroup (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (U : Subgroup H) [U.Normal] (hU : U ≤ q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (hindex : (centralizer (A : Set H)).relIndex U ≤ 8)
    (X : Subgroup H) [X.Normal] (hXU : X ≤ U) :
    ⁅X, pResidual 2 H⁆ = ⊥ ∨ ⁅U, pResidual 2 H⁆ ≤ X := by
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hU2 : IsPGroup 2 U := hp.of_injective (inclusion hU) (inclusion_injective hU)
  have hs := noncentralCount_le_one_of_le_ker q hq hp U hU A a ha haA hindex s
  by_cases hz : s.noncentralCount = 0
  · right
    have hlast : IsPGroup 2 s.series.last.val := by
      rw [s.last_eq]
      exact hU2
    have h := s.series.residual_commutator_le_head_of_central_steps
      hlast (s.noncentralCount_eq_zero_iff.mp hz)
    rw [s.last_eq, s.head_eq] at h
    change ⁅U, pResidual 2 H⁆ ≤ ⊥ at h
    exact h.trans bot_le
  · exact s.residual_dichotomy_of_count_one hU2 (by omega) X hXU

/-- Every normal subgroup of V either centralizes the residual modulo Z or
contains the whole residual movement modulo Z. The two-group V/Z is not
assumed abelian. -/
theorem residual_dichotomy_modulo
    (q : H →* alternatingGroup (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (hindex : (centralizerModulo V A Z).relIndex V ≤ 8)
    (X : Subgroup H) [X.Normal] (hXV : X ≤ V) :
    ⁅X, pResidual 2 H⁆ ≤ Z ∨ ⁅V, pResidual 2 H⁆ ≤ X ⊔ Z := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q (hZV.trans hV)
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker = q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (V.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  let : (X.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  have hVbar : V.map π ≤ qbar.ker := by rw [hker]; exact map_mono hV
  have hAbar : (A.map π).map qbar = A.map q := by
    rw [map_map]
    rfl
  have hidxbar : (centralizer (A.map π : Set (H ⧸ Z))).relIndex (V.map π) ≤ 8 := by
    rwa [centralizerModulo_relIndex_eq] at hindex
  have h := residual_dichotomy qbar hqbar hpbar (V.map π) hVbar (A.map π) a ha
    (hAbar.symm ▸ haA) hidxbar (X.map π) (map_mono hXV)
  have hres : (pResidual 2 H).map π = pResidual 2 (H ⧸ Z) := map_pResidual_quotient 2 Z
  rcases h with h | h
  · left
    have hm : (⁅X, pResidual 2 H⁆).map π ≤ ⊥ := by
      rw [map_commutator, hres, h]
    have hk := (map_le_iff_le_comap).mp hm
    simpa only [MonoidHom.comap_bot, π, QuotientGroup.ker_mk'] using hk
  · right
    have hm : (⁅V, pResidual 2 H⁆).map π ≤ X.map π := by
      rwa [map_commutator, hres]
    have hk := (map_le_iff_le_comap).mp hm
    simpa only [comap_map_eq, π, QuotientGroup.ker_mk'] using hk

/-- The original source commutator, with P equal to the actual A₆ kernel. -/
theorem kernel_commutator_residual_dichotomy
    (q : H →* alternatingGroup (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (hindex : (centralizerModulo V A Z).relIndex V ≤ 8) :
    ⁅⁅V, q.ker⁆, pResidual 2 H⁆ ≤ Z ∨ ⁅V, pResidual 2 H⁆ ≤ ⁅V, q.ker⁆ ⊔ Z := by
  exact residual_dichotomy_modulo q hq hp V Z hZV hV A a ha haA hindex
    ⁅V, q.ker⁆ (commutator_le_left V q.ker)

/-- The source form retaining the original subgroup K and its commutator
centralization modulo Z, rather than a quotient-action compatibility premise. -/
theorem kernel_commutator_residual_dichotomy_of_index
    (q : H →* alternatingGroup (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z : Subgroup H) [V.Normal] [Z.Normal] (hZV : Z ≤ V) (hV : V ≤ q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 2) (haA : a ∈ A.map q)
    (K : Subgroup H) (hc : ⁅V ⊓ K, A⁆ ≤ Z) (hindex : K.relIndex V ≤ 8) :
    ⁅⁅V, q.ker⁆, pResidual 2 H⁆ ≤ Z ∨ ⁅V, pResidual 2 H⁆ ≤ ⁅V, q.ker⁆ ⊔ Z :=
  kernel_commutator_residual_dichotomy q hq hp V Z hZV hV A a ha haA
    ((centralizerModulo_relIndex_le_of_commutator V A Z K hc).trans hindex)

/-- With a fixed derived group and full residual movement, the unique
noncentral chief factor leaves no proper normal layer outside the center. -/
theorem normal_subgroup_central_or_cover
    (q : H →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (hp : IsPGroup 2 q.ker) (P : Subgroup H) [P.Normal] (hP : P ≤ q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2)
    (haA : a ∈ A.map q)
    (hindex : (centralizerModulo P A (P ⊓ centralizer (P : Set H))).relIndex P ≤ 8)
    (hfull : ⁅P,pResidual 2 H⁆ = P)
    (hfixed : ⁅⁅P,P⁆,pResidual 2 H⁆ = ⊥)
    (Y : Subgroup H) [Y.Normal] (hYP : Y ≤ P) :
    Y ≤ P ⊓ centralizer (P : Set H) ∨
      P ≤ Y ⊔ (P ⊓ centralizer (P : Set H)) := by
  let C := P ⊓ centralizer (P : Set H)
  rcases residual_dichotomy_modulo q hq hp P C inf_le_left hP A a ha haA hindex Y hYP
    with hf | hc
  · left
    have h₁ : ⁅⁅P,Y⁆,pResidual 2 H⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono (commutator_mono le_rfl hYP) le_rfl).trans hfixed.le)
    have h₂ : ⁅⁅Y,pResidual 2 H⁆,P⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hf.trans inf_le_right)
    have hz := commutator_commutator_eq_bot_of_rotate h₁ h₂
    rw [commutator_comm (pResidual 2 H) P,hfull,commutator_comm] at hz
    exact le_inf hYP (commutator_eq_bot_iff_le_centralizer.mp hz)
  · right
    rwa [hfull] at hc

/-- In particular the original two-kernel acts trivially on the central
quotient. The covering branch is eliminated by nilpotent saturation. -/
theorem kernel_commutator_le_center
    (q : H →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (hp : IsPGroup 2 q.ker) (P : Subgroup H) [P.Normal] (hP : P ≤ q.ker)
    (A : Subgroup H) (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2)
    (haA : a ∈ A.map q)
    (hindex : (centralizerModulo P A (P ⊓ centralizer (P : Set H))).relIndex P ≤ 8)
    (hfull : ⁅P,pResidual 2 H⁆ = P)
    (hfixed : ⁅⁅P,P⁆,pResidual 2 H⁆ = ⊥) :
    ⁅P,q.ker⁆ ≤ P ⊓ centralizer (P : Set H) := by
  rcases normal_subgroup_central_or_cover q hq hp P hP A a ha haA hindex hfull hfixed
    ⁅P,q.ker⁆ (commutator_le_left _ _) with hc | hc
  · exact hc
  · have hPC : P ≤ P ⊓ centralizer (P : Set H) :=
      le_of_le_sup_commutator_of_isNilpotent q.ker P
        (P ⊓ centralizer (P : Set H)) q.ker hp.isNilpotent hP
        (inf_le_left.trans hP) le_rfl le_normalizer_of_normal
        (by rwa [sup_comm] at hc)
    exact (commutator_le_left _ _).trans hPC

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.AlternatingBudget
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
