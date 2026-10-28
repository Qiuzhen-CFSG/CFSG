module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Uniqueness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Eight
public import Theory.GroupTheory.OddIntersectionInvolutionProduct

/-!
# The marked Omega identity in Lemma 16.4(b)

The intersection of the distinguished circle L with C_B(L) embeds into its
odd center. Square-root correction therefore splits every involution of
L C_B(L) into involutions in the two commuting factors. Lemma 16.4(a)
identifies the centralizer factor with the marked involution u. Intersecting
with the actual selected two-subgroup gives Ω₁(T) = Q⟨u⟩.

Source: GLS IV, Chapter 2, Lemma 16.4(b), the last equality.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem marked_root_le_circle {u t : G} (ht : t ∈ Z)
    (htu : Commute t u) :
    closure (residualCentralizerTrace Z M u) ⊔ zpowers t ≤
      localCircleIn Z (centralizer ({u} : Set G)) := by
  rw [localCircleIn_eq_closure]
  apply sup_le
  · apply Subgroup.closure_mono
    intro x hx
    exact ⟨hx.1,mem_centralizer_singleton_iff.mpr hx.2.2.eq⟩
  · exact zpowers_le.mpr (subset_closure ⟨ht,mem_centralizer_singleton_iff.mpr htu.eq⟩)

/-- The marked involution is the unique involution of the actual relative
centralizer C_B(B°), by the root-centralizer uniqueness theorem. -/
public theorem source16_unique_involution_circle_centralizer
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    {v : G} (hv : PFAppendixIII.IsInvolution v)
    (hvB : v ∈ centralizer ({u} : Set G))
    (hvC : v ∈ centralizer (localCircleIn Z (centralizer ({u} : Set G)) : Set G)) :
    v = u :=
  source16_unique_involution_marked_root_centralizer h r ha hg hz hzM ht htM hu huD
    hzu htu hmax hv (mem_centralizer_singleton_iff.mp hvB)
      (centralizer_le (marked_root_le_circle ht htu) hvC)

/-- The last equality of 16.4(b), with literal ambient T₁, L = B° and
J = C_B(L). The odd center and unique involution premises are derived. -/
public theorem source16_omega_intersection_circle_centralizer
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (T₁ : Subgroup G) (huT : u ∈ T₁) :
    let B := centralizer ({u} : Set G)
    let L := localCircleIn Z B
    let J := B ⊓ centralizer (L : Set G)
    omegaOneAmbient (T₁ ⊓ (L ⊔ J)) = omegaOneAmbient (T₁ ⊓ L) ⊔ zpowers u := by
  let B := centralizer ({u} : Set G)
  let L := localCircleIn Z B
  let J := B ⊓ centralizer (L : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  have hf := localCircleHom_injective Z B
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  have hBM : ¬ B ≤ M := fun hh => htM (hh (mem_centralizer_singleton_iff.mpr htu.eq))
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M :=
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩
  have hc := (localCircle_nonsolvable_structure h r ha B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM hne hns).1
  have hoddC : Odd (Nat.card (center C)) := by
    rw [← hc]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  have hinter : L ⊓ J ≤ (center C).map f := by
    intro x hx
    obtain ⟨xB,hxC,rfl⟩ := hx.1
    let xC : C := ⟨xB,hxC⟩
    refine ⟨xC,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply hf
    rw [map_mul,map_mul]
    exact hx.2.2 (f y) (mem_map_of_mem B.subtype y.property)
  have hodd : Odd (Nat.card (L ⊓ J : Subgroup G)) := by
    have himage : Odd (Nat.card ((center C).map f)) := by
      rw [card_map_of_injective hf]
      exact hoddC
    exact himage.of_dvd_nat (card_dvd_of_le hinter)
  have huJ : u ∈ J := by
    refine ⟨mem_centralizer_singleton_iff.mpr rfl,?_⟩
    intro x hx
    exact mem_centralizer_singleton_iff.mp (localCircleIn_le Z B hx)
  exact omega_inf_commuting_join_of_unique_involution L J T₁ inf_le_right hodd
    huJ huT hu.sq_eq_one (by
      intro b hb hb2
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · exact Or.inr (source16_unique_involution_circle_centralizer h r ha hg hz hzM ht htM
          hu huD hzu htu hmax ⟨hb1,hb2⟩ hb.1 hb.2))

end BenderSuzuki.ZD
