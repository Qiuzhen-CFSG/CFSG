module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearCubicResidual
public import Theory.GroupTheory.SolvableResidual.TwoKernel
public import Theory.GroupTheory.CentralCommutatorQuotient
public import Theory.GroupTheory.PCoreRestriction

/-!
# The moved-core split in the original linear centralizer argument

The original Cartan X lies in H = N_L(X₁)^∞. Indeed N_L(X₁) covers
L/O₂(L), so its two-residual is its solvable residual; its two-group
quotient kills every odd subgroup, including the entire Cartan.

For U ≤ T, C_U(X₁) normalizes H. Put Y = [C_U(X₁),X]. If Y lies in
O₂(LT), then it lies in H ∩ O₂(LT) ≤ O₂(H). When [O₂(H),H] = 1,
commutation with each element of C_U(X₁) is a homomorphism from the
odd group X into the central two-group O₂(H), hence is trivial.
Consequently Y ≠ 1 either forces [O₂(H),H] ≠ 1 or forces both Y and U
to escape O₂(LT). This proves the escape step needed for G.2.5 without
the stronger intermediate factorization involving O₂(L₁).

The consumer uses the literal U = ⟨V^{C_G(V₁)}⟩ and the same common-Q
configuration, full SL₃(4) quotient and ambient cubic-normalizer escape.
Containment U ≤ T from G.2.2 and nonzero Y from the extraspecial Sylow-three
action remain explicit source inputs owned here. Their construction,
the two subsequent centralizer/module branches, the stronger O₂(L₁)
factorization if needed, common-normal existence, both orientations and
full 11.1.1--3 assembly remain with qt-d-1222-natural-relative-components.
Original earlier-source inputs retain their producers and final discharge
by qt-d-1222-natural-local-geometry. This is not the SL₃(4) exclusion.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 11.1.2,
printed p.763, the paragraph defining Y before the application of G.2.5.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section

private theorem odd_le_residual_of_perfect_two_kernel
    {A B : Type*} [Group A] [Finite A] [Group B] [Group.IsPerfect B]
    (q : A →* B) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (X : Subgroup A) (ho : Odd (Nat.card X)) : X ≤ solvableResidual A := by
  rw [←pResidual_eq_solvableResidual_of_perfect_image q hq hk]
  apply le_pResidual_of_isPPerfect
  intro N hn hp
  let := hn
  apply index_eq_one.mp
  change Nat.card (X ⧸ N) = 1
  exact hp.card_eq_or_dvd.resolve_right
    (fun hd => ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))

private theorem odd_commutator_eq_bot_of_central_two_core
    {G : Type*} [Group G] [Finite G] {H C A B : Subgroup G}
    (hHB : H ≤ B) (hCH : C ≤ normalizer (H : Set G))
    (hAH : A ≤ H) (hodd : Odd (Nat.card A))
    (hcore : ⁅H.pCoreIn 2,H⁆ = ⊥) (hY : ⁅C,A⁆ ≤ B.pCoreIn 2) :
    ⁅C,A⁆ = ⊥ := by
  have hYH : ⁅C,A⁆ ≤ H :=
    (commutator_mono le_rfl hAH).trans (le_normalizer_iff_commutator_le_right.mp hCH)
  have hYR : ⁅C,A⁆ ≤ H.pCoreIn 2 :=
    (le_inf hYH hY).trans (inf_pCoreIn_le_of_le 2 hHB)
  have hRA : H.pCoreIn 2 ≤ centralizer (A : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hcore).trans (centralizer_le hAH)
  apply bot_unique
  apply commutator_le.mpr
  intro c hc a ha
  let φ := centralCommutatorHom A (H.pCoreIn 2) hRA c
    (fun x hx => hYR (commutator_mem_commutator hc hx))
  have hp : IsPGroup 2 φ.range := (isPGroup_pCoreIn 2 H).to_subgroup _
  have hcard : Nat.card φ.range = 1 := hp.card_eq_or_dvd.resolve_right
    (fun hd => hodd.not_two_dvd_nat (hd.trans (card_range_dvd φ)))
  have hbot : φ.range = ⊥ := card_eq_one.mp hcard
  have he : φ ⟨a,ha⟩ = 1 := hbot.le ⟨⟨a,ha⟩,rfl⟩
  exact congrArg Subtype.val he

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The entire original Cartan lies in the cubic normalizer residual. -/
theorem linear_four_cartan_le_cubic_residual
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3) :
    X ≤ localResidual L (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) := by
  let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  let N := L ⊓ normalizer (E : Set G)
  let H := localResidual L E
  let c := Coordinates.sl3 m
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  let : IsMulCommutative X := .of_comm fun a b => (c.cartanTorusEquiv hX).injective
    (by simp only [map_mul,mul_comm])
  have hXN : X ≤ N := le_inf (hX.1.trans inf_le_left)
    ((X.le_centralizer.trans (centralizer_le (show E ≤ X from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _))
  let q := (QuotientGroup.mk' (pCore 2 L)).comp (inclusion (show N ≤ L from inf_le_left))
  obtain ⟨_,_,_,_,e,he⟩ := linear_four_cubic_normalizer_residual D S m f hd hX hcard
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨u,hu⟩ := e.surjective (c.groupEquiv z)
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) u
    refine ⟨⟨h,localResidual_le E h.property⟩,?_⟩
    exact c.groupEquiv.injective ((he h).symm.trans hu)
  have hk : IsPGroup 2 q.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have ho : Odd (Nat.card (X.subgroupOf N)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv]
    exact hX.odd
  have hr := odd_le_residual_of_perfect_two_kernel q hq hk (X.subgroupOf N) ho
  intro x hx
  exact mem_map_of_mem N.subtype (hr (show (⟨x,hXN hx⟩ : N) ∈ X.subgroupOf N from hx))

/-- A nonzero commutator of the cubic-fixed part of U with the original X either
moves the two-core of L_X₁ or escapes the original two-core of LT. -/
theorem linear_four_cubic_commutator_moves_or_escapes
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X U : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hUT : U ≤ (T : Subgroup G))
    (hY : ⁅U ⊓ centralizer
      ((X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) : Set G),
        X⁆ ≠ ⊥) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    ⁅H.pCoreIn 2,H⁆ ≠ ⊥ ∨
      ¬ ⁅U ⊓ centralizer (E : Set G),X⁆ ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  let H := localResidual L E
  let C := U ⊓ centralizer (E : Set G)
  have hCH : C ≤ normalizer (H : Set G) :=
    ((le_inf ((inf_le_left.trans hUT).trans D.sylow_normalizes_component)
      ((inf_le_right.trans (Subgroup.centralizer_le_normalizer _)).trans
        (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  by_cases hz : ⁅H.pCoreIn 2,H⁆ = ⊥
  · right
    intro hle
    exact hY (odd_commutator_eq_bot_of_central_two_core
      (((localResidual_le E).trans inf_le_left).trans le_sup_left) hCH
      (linear_four_cartan_le_cubic_residual D S m f hd hX hcard)
      hX.odd hz hle)
  · exact .inl hz

/-- In the branch where L_X₁ centralizes its two-core, a nonzero original
cubic commutator forces U outside O₂(LT), as required by G.2.5. -/
theorem linear_four_span_escapes_of_central_cubic_core
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {X U : Subgroup G} (hX : IsCartan T L X)
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hUT : U ≤ (T : Subgroup G))
    (hY : ⁅U ⊓ centralizer
      ((X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) : Set G),
        X⁆ ≠ ⊥)
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer (f.Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    ¬ U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hout := (linear_four_cubic_commutator_moves_or_escapes D S m f hd hX hcard hUT hY).resolve_left
    (fun hn => hn hzero)
  intro hU
  apply hout
  have hn : X ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    ((hX.1.trans inf_le_left).trans
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact (commutator_mono (inf_le_left.trans hU) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hn)

/-- The literal source span U = ⟨V^{C_G(V₁)}⟩ enters the two branches of the
centralizer argument. Its containment in T is the G.2.2 input; nonzero Y
is the extraspecial Sylow-three action input. Their construction, as well
as the subsequent G.2.5 and B.4.14 comparison, stays with this source owner. -/
theorem linear_triangle_cubic_core_dichotomy_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    U ≤ (T : Subgroup G) →
    ⁅U ⊓ centralizer (E : Set G),X⁆ ≠ ⊥ →
    E ≤ H ∧ X ≤ H ∧ H ≤ centralizer (E : Set G) ∧
    Source.IsSL (H ⧸ pCore 2 H) 3 4 ∧
    H.pCoreIn 2 = H ⊓ L.pCoreIn 2 ∧ H ⊔ L.pCoreIn 2 = L ∧
    V = ⁅V,H⁆ ∧ ¬ normalizer (E : Set G) ≤ normalizer (L : Set G) ∧
    (⁅H.pCoreIn 2,H⁆ ≠ ⊥ ∨
      (¬ ⁅U ⊓ centralizer (E : Set G),X⁆ ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  intro E H U hUT hY
  have hc : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3 := by
    rwa [linear_four_cartan_kernels_eq D S m hd f hX]
  obtain ⟨hEH,hHC,hmodel,hcore,hcover,_,hact,hout⟩ :=
    linear_triangle_centralizer_setup_of_common_normal D S m f hd hfix hX hK hLK
      hK₀ hK₀K hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ
  refine ⟨hEH,linear_four_cartan_le_cubic_residual D S m f hd hX hc,
    hHC,hmodel,hcore,hcover,hact,hout,?_⟩
  by_cases hz : ⁅H.pCoreIn 2,H⁆ = ⊥
  · right
    exact ⟨(linear_four_cubic_commutator_moves_or_escapes D S m f hd hX hc hUT hY).resolve_left
      (fun hn => hn hz),linear_four_span_escapes_of_central_cubic_core D S m f hd hX hc hUT hY hz⟩
  · exact .inl hz

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
