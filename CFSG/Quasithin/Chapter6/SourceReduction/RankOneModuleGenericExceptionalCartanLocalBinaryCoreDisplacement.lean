module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinarySeven

/-!
# Core stabilizers and quintic displacement in the original binary row

Let X = CT be the original component--Sylow join. Every nontrivial
X-invariant two-subgroup has stabilizer in L exactly N_L(T intersect L).
Indeed a full L-stabilizer would put X inside N_G(L) by maximal-local
uniqueness, contradicting the original HStar escape. Rank-one Borel
uniqueness gives the reverse bound, and the original Cartan lies in X.
This applies to O₂(X) and every nontrivial characteristic subgroup of it.

The quintic in O²(C_L(B)) constructed in LocalBinarySeven lies outside X.
Adjoining it to X already generates L join X: a proper intersection with L
would lie in the same Borel, which is contained in X. Maximal-local
uniqueness shows that this larger generated subgroup has trivial two-core.
The SAME quintic moves every nontrivial X-invariant two-subgroup, hence
every nontrivial characteristic subgroup of the retained O₂(X).

These conclusions constrain the actual core configuration; they do not
remove the kernel U intersect O₂(X) from the earlier quotient bound.
Excluding binary triality and constructing the full exceptional-component
witness remain with the original local Cartan assembly.

Source: Aschbacher--Smith 5.1.5, 5.1.10--13, printed pp.631,634--638,
with maximal-local uniqueness 1.2.7, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem invariant_two_subgroup_stabilizer
    {T : Sylow 2 G} {L W H A B X N : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hHX : H ≤ X) (hAX : A ≤ X)
    (hN : IsPGroup 2 N) (hN0 : N ≠ ⊥)
    (hXN : X ≤ normalizer (N : Set G)) :
    L ⊓ normalizer (N : Set G) = localBorel T L := by
  have hTX : (T : Subgroup G) ≤ X := hH.1.1.2.trans hHX
  have hLN : ¬ L ≤ normalizer (N : Set G) := by
    intro hn
    have hh := normalizer_le_of_unique_maximalTwoLocal h.unique_local_join hN hN0
      (sup_le hn (hTX.trans hXN))
    exact hH.1.2 (hHX.trans (hXN.trans hh))
  apply le_antisymm
  · exact le_inf inf_le_left ((le_inf (inf_le_left.trans L.le_normalizer) inf_le_right).trans
      (intersection_normalizes_localSylow h.linear h.sylow_normalizes (hTX.trans hXN) hLN))
  · rw [←c.left_sup_intersection h.sylow_normalizes]
    exact le_inf (sup_le inf_le_right (c.left_le.trans inf_le_left))
      ((sup_le (inf_le_left.trans hTX) hAX).trans hXN)

private theorem quintic_generated_core_free
    {T : Sylow 2 G} {L W H A B X F : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hHX : H ≤ X) (hAX : A ≤ X)
    (hFL : F ≤ L) (hFX : ¬ F ≤ X) :
    F ⊔ X = L ⊔ X ∧ (F ⊔ X).pCoreIn 2 = ⊥ ∧
      ∀ N : Subgroup G, IsPGroup 2 N → N ≠ ⊥ →
        X ≤ normalizer (N : Set G) → ¬ F ≤ normalizer (N : Set G) := by
  have hTX : (T : Subgroup G) ≤ X := hH.1.1.2.trans hHX
  have hBX : localBorel T L ≤ X := by
    rw [←c.left_sup_intersection h.sylow_normalizes]
    exact sup_le (inf_le_left.trans hTX) hAX
  have hLF : L ≤ F ⊔ X := by
    by_contra hn
    have hi := intersection_normalizes_localSylow h.linear h.sylow_normalizes
      (hTX.trans le_sup_right) hn
    apply hFX
    exact (le_inf hFL ((le_inf (hFL.trans L.le_normalizer) le_sup_left).trans hi)).trans hBX
  have he : F ⊔ X = L ⊔ X := le_antisymm (sup_le_sup_right hFL X) (sup_le hLF le_sup_right)
  have hz : (F ⊔ X).pCoreIn 2 = ⊥ := by
    by_contra hn
    have hnorm : F ⊔ X ≤ normalizer ((F ⊔ X).pCoreIn 2 : Set G) :=
      (F ⊔ X).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (F ⊔ X) (pCore 2 (F ⊔ X : Subgroup G)))
    have hh := normalizer_le_of_unique_maximalTwoLocal h.unique_local_join
      (isPGroup_pCoreIn 2 (F ⊔ X : Subgroup G)) hn
      ((sup_le hLF (hTX.trans le_sup_right)).trans hnorm)
    exact hH.1.2 (hHX.trans (le_sup_right.trans (hnorm.trans hh)))
  refine ⟨he,hz,?_⟩
  intro N hN hN0 hXN hFN
  have hs := invariant_two_subgroup_stabilizer h hH c hHX hAX hN hN0 hXN
  exact hFX (((le_inf hFL hFN).trans_eq hs).trans hBX)

/-- Every nontrivial two-subgroup normalized by the original containing
component--Sylow join has exactly the original Borel as its stabilizer in L. -/
theorem original_binary_triality_core_stabilizers
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let Q := X.pCoreIn 2
    L ⊓ normalizer (Q : Set G) = localBorel T L ∧
      ∀ D : Subgroup Q, D.Characteristic → D ≠ ⊥ →
        L ⊓ normalizer (D.map Q.subtype : Set G) = localBorel T L := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  obtain ⟨_,hX,hAX,_⟩ := original_binary_triality_core_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  refine ⟨invariant_two_subgroup_stabilizer h hH c hX.2 hAX
    (isPGroup_pCoreIn 2 X) hX.1 hXQ,?_⟩
  intro D hD hD0
  let := hD
  have hN0 : D.map Q.subtype ≠ ⊥ := by
    intro he
    exact hD0 ((D.map_eq_bot_iff_of_injective Q.subtype_injective).mp he)
  exact invariant_two_subgroup_stabilizer h hH c hX.2 hAX
    (((isPGroup_pCoreIn 2 X).to_subgroup D).map Q.subtype) hN0
    (hXQ.trans (normalizer_le_normalizer_characteristic_image Q D))

/-- A single quintic in the original seven-centralizer generates the same
join with CT as L, with trivial two-core. It moves every nontrivial
characteristic subgroup of the retained two-core. -/
theorem original_binary_triality_quintic_core_displacement
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let Q := X.pCoreIn 2
    let R := residual (L ⊓ centralizer (B : Set G))
    ∃ F : Subgroup G, F ≤ R ∧ Nat.card F = 5 ∧ F ≤ centralizer (B : Set G) ∧
      F ⊔ X = L ⊔ X ∧ (F ⊔ X).pCoreIn 2 = ⊥ ∧
      ¬ F ≤ normalizer (Q : Set G) ∧
      (∀ D : Subgroup Q, D.Characteristic → D ≠ ⊥ →
        ¬ F ≤ normalizer (D.map Q.subtype : Set G)) ∧
      (∀ N : Subgroup G, IsPGroup 2 N → N ≠ ⊥ →
        X ≤ normalizer (N : Set G) → ¬ F ≤ normalizer (N : Set G)) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  obtain ⟨_,hX,hAX,_⟩ := original_binary_triality_core_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨F,hFR,hF,hFB,hFX⟩ := original_binary_triality_seven_quintic_escape
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hFL : F ≤ L := hFR.trans ((map_subtype_le _).trans inf_le_left)
  obtain ⟨he,hz,hmoves⟩ := quintic_generated_core_free h hH c hX.2 hAX hFL hFX
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  refine ⟨F,hFR,hF,hFB,he,hz,hmoves Q (isPGroup_pCoreIn 2 X) hX.1 hXQ,?_,hmoves⟩
  intro D hD hD0
  let := hD
  have hN0 : D.map Q.subtype ≠ ⊥ := by
    intro he
    exact hD0 ((D.map_eq_bot_iff_of_injective Q.subtype_injective).mp he)
  exact hmoves _ (((isPGroup_pCoreIn 2 X).to_subgroup D).map Q.subtype) hN0
    (hXQ.trans (normalizer_le_normalizer_characteristic_image Q D))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
