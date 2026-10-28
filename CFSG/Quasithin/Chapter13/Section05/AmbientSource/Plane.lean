module
public import Theory.GroupTheory.PlaneCoreNormalClosure
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage

/-!
# The actual four-group action in Lemma 13.3.15

The normalizer of the source plane acts on its three nonidentity elements.
The point-core lies in the original Sylow, fixes the source point and,
assuming the preceding noncentrality theorem, has transposition image.
The cubic parabolic then fills this action. Its kernel on the generated
product is a two-group, so the product is the actual normal closure and
its two-residual is the original parabolic.

The source noncentrality theorem 13.3.14 and the preceding marked cubic
parabolic action remain named inputs. Neither is inferred from a natural
module alone. Source: Aschbacher–Smith, pp.893–894, 13.3.15(1–4).
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsKleinFour
namespace CFSG.Quasithin.Chapter13.Section05.AmbientSource
variable {G : Type*} [Group G]

/-- The literal conjugation action of the plane normalizer. -/
def planeAction (E : Subgroup G) [IsKleinFour E] :
    normalizer (E : Set G) →* Equiv.Perm (Fin 3) :=
  (IsKleinFour.autEquivPermThree E).toMonoidHom.comp E.normalizerMonoidHom

theorem planeAction_eq_one (E : Subgroup G) [IsKleinFour E]
    (g : normalizer (E : Set G)) : planeAction E g = 1 ↔ g.val ∈ centralizer (E : Set G) := by
  change IsKleinFour.autEquivPermThree E (E.normalizerMonoidHom g) = 1 ↔ _
  rw [(IsKleinFour.autEquivPermThree E).map_eq_one_iff]
  constructor
  · intro he
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg (fun a : MulAut E => ((a ⟨x,hx⟩ : E) : G)) he
    change g.val * x * g.val⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg
    ext x
    change g.val * x.val * g.val⁻¹ = x.val
    rw [← mem_centralizer_iff.mp hg x.val x.property, mul_inv_cancel_right]

/-- The actual point-core lies in the original Sylow and normalizes the plane. -/
theorem point_core_le_plane_normalizer (T : Sylow 2 G) (P E : Subgroup G)
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (hTE : (T : Subgroup G) ≤ normalizer (E : Set G)) :
    (normalizer (P : Set G)).pCoreIn 2 ≤ normalizer (E : Set G) := by
  have hh := pCoreIn_le_sylow (normalizer (P : Set G)) (T.subtype hTP)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTP] at hh
  exact hh.trans hTE

/-- The kernel of the plane action normalizes the point-core, because it
centralizes the point itself. -/
theorem plane_kernel_normalizes_point_core (P E : Subgroup G) [IsKleinFour E]
    (hPE : P ≤ E) :
    (planeAction E).ker ≤ normalizer
      (((normalizer (P : Set G)).pCoreIn 2).subgroupOf (normalizer (E : Set G)) : Set (normalizer (E : Set G))) := by
  apply le_normalizer_iff.mpr
  intro g hg q hq
  have hgc : g.val ∈ centralizer (E : Set G) := (planeAction_eq_one E g).mp hg
  have hgp : g.val ∈ normalizer (P : Set G) :=
    centralizer_le_normalizer _ (centralizer_le hPE hgc)
  have hn : normalizer (P : Set G) ≤ normalizer
      ((normalizer (P : Set G)).pCoreIn 2 : Set G) :=
    (normalizer (P : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact le_normalizer_iff.mp hn g.val hgp q.val hq

/-- Noncentrality of the point-core on the plane gives exactly a
transposition image. This uses only the source point of order two. -/
theorem point_core_image_card_two (T : Sylow 2 G) (P E : Subgroup G) [IsKleinFour E]
    (hP : Nat.card P = 2) (hPE : P ≤ E)
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (hTE : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hm : ⁅(normalizer (P : Set G)).pCoreIn 2, E⁆ ≠ ⊥) :
    Nat.card ((((normalizer (P : Set G)).pCoreIn 2).subgroupOf
      (normalizer (E : Set G))).map (planeAction E)) = 2 := by
  let Q := (normalizer (P : Set G)).pCoreIn 2
  let N := normalizer (E : Set G)
  have hQN : Q ≤ N := point_core_le_plane_normalizer T P E hTP hTE
  let A := (Q.subgroupOf N).map E.normalizerMonoidHom
  have ha : Nat.card A ≤ 2 := by
    have hp : P ≠ ⊥ := by intro he; simp [he] at hP
    obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hp
    let zE : E := ⟨z.val,hPE z.property⟩
    apply card_mulAut_subgroup_le_two_of_fixed_point (IsKleinFour.card_four (G := E)) zE
      (fun he => hz (Subtype.ext (congrArg (fun w : E => w.val) he))) A
    rintro a ⟨q,hq,rfl⟩
    apply Subtype.ext
    change q.val * z.val * q.val⁻¹ = z.val
    have hc := normalizer_le_centralizer_of_card_two P hP ((pCoreIn_le 2 _) hq)
    have hh := mem_centralizer_iff.mp hc z.val z.property
    change z.val * q.val = q.val * z.val at hh
    rw [← hh, mul_inv_cancel_right]
  have hn : A ≠ ⊥ := by
    intro he
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro q hq
    have hf : E.normalizerMonoidHom ⟨q,hQN hq⟩ = 1 := by
      have hh : E.normalizerMonoidHom ⟨q,hQN hq⟩ ∈ A := ⟨⟨q,hQN hq⟩,hq,rfl⟩
      rw [he] at hh
      exact hh
    apply (planeAction_eq_one E ⟨q,hQN hq⟩).mp
    change IsKleinFour.autEquivPermThree E (E.normalizerMonoidHom ⟨q,hQN hq⟩) = 1
    rw [hf, map_one]
  have hcA : Nat.card A = 2 := by
    have := A.one_lt_card_iff_ne_bot.mpr hn
    omega
  rw [planeAction, ← map_map, Subgroup.card_map_of_injective (IsKleinFour.autEquivPermThree E).injective]
  exact hcA

/-- The original normal closure and normalization assertions of 13.3.15.
The cubic parabolic's local action data precede this argument; the only
ambient noncentrality input is the conclusion of 13.3.14. -/
theorem plane_normalClosure [Finite G] (T : Sylow 2 G)
    (P E X : Subgroup G) [IsKleinFour E]
    (hP : Nat.card P = 2) (hPE : P ≤ E)
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (hTE : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hXN : X ≤ normalizer (E : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X)
    (hx : Nat.card ((X.subgroupOf (normalizer (E : Set G))).map (planeAction E)) = 3)
    (hkX : IsPGroup 2 (X ⊓ centralizer (E : Set G) : Subgroup G))
    (hm : ⁅(normalizer (P : Set G)).pCoreIn 2, E⁆ ≠ ⊥) :
    conjugateSpanBy ((normalizer (P : Set G)).pCoreIn 2) (normalizer (E : Set G)) =
        X ⊔ (normalizer (P : Set G)).pCoreIn 2 ∧
      normalizer (E : Set G) ≤ normalizer (X : Set G) ∧
      (X ⊔ (normalizer (P : Set G)).pCoreIn 2).pCoreIn 2 =
        (X ⊔ (normalizer (P : Set G)).pCoreIn 2) ⊓ centralizer (E : Set G) ∧
      Nonempty (((X ⊔ (normalizer (P : Set G)).pCoreIn 2 : Subgroup G) ⧸
        pCore 2 (X ⊔ (normalizer (P : Set G)).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let N := normalizer (E : Set G)
  let Q := (normalizer (P : Set G)).pCoreIn 2
  let X' := X.subgroupOf N
  let Q' := Q.subgroupOf N
  let f := planeAction E
  have hQN : Q ≤ N := point_core_le_plane_normalizer T P E hTP hTE
  have hQT : Q ≤ T := by
    have hh := pCoreIn_le_sylow (normalizer (P : Set G)) (T.subtype hTP)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTP] at hh
  have hpX : IsPPerfect 2 X' := hX.of_surjective
    (subgroupOfEquivOfLe hXN).symm.toMonoidHom (subgroupOfEquivOfLe hXN).symm.surjective
  have hpQ : IsPGroup 2 Q' := (isPGroup_pCoreIn 2 _).comap_subtype
  have hn : Q' ≤ normalizer (X' : Set N) := by
    apply le_normalizer_iff.mpr
    intro q hq x hx
    exact le_normalizer_iff.mp hTX q.val (hQT hq) x.val hx
  have hq : Nat.card (Q'.map f) = 2 := point_core_image_card_two T P E hP hPE hTP hTE hm
  have hk : IsPGroup 2 (X' ⊓ f.ker : Subgroup N) := by
    have he : X' ⊓ f.ker = (X ⊓ centralizer (E : Set G)).subgroupOf N := by
      ext g
      exact and_congr_right (fun _ => planeAction_eq_one E g)
    rw [he]
    exact hkX.comap_subtype
  have hdis : Disjoint (X'.map f) (Q'.map f) :=
    disjoint_of_coprime_natCard (by rw [hx,hq]; decide)
  have hkJ := join_inf_ker_isPGroup_of_disjoint_images f X' Q' hn hk hpQ hdis
  have hcover := permThree_join_image_eq_top f X' Q' hx hq
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    exact top_unique (hcover ▸ map_le_range f (X' ⊔ Q'))
  have hker := plane_kernel_normalizes_point_core P E hPE
  have he := conjugateSpan_eq_join_of_permThree f hf X' Q' hpX hcover hq hkJ hker
  have hnX := normalizes_parabolic_of_permThree f hf X' Q' hpX hpQ hn hcover hq hkJ hker
  have hJ : (X' ⊔ Q').map N.subtype = X ⊔ Q := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXN,map_subgroupOf_eq_of_le hQN]
  have hkmap : ((X' ⊔ Q') ⊓ f.ker).map N.subtype = (X ⊔ Q) ⊓ centralizer (E : Set G) := by
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      refine ⟨?_,(planeAction_eq_one E g).mp hg.2⟩
      rw [← hJ]
      exact mem_map_of_mem _ hg.1
    · intro g hg
      obtain ⟨j,hj,hjg⟩ := (show g ∈ (X' ⊔ Q').map N.subtype by rw [hJ]; exact hg.1)
      refine ⟨j,⟨hj,?_⟩,hjg⟩
      apply (planeAction_eq_one E j).mpr
      change N.subtype j ∈ centralizer (E : Set G)
      rw [hjg]
      exact hg.2
  have hkAmbient : IsPGroup 2 ((X ⊔ Q) ⊓ centralizer (E : Set G) : Subgroup G) :=
    hkmap ▸ hkJ.map N.subtype
  let I := X ⊔ Q
  have hIN : I ≤ N := sup_le hXN hQN
  let φ := f.comp (inclusion hIN)
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨j,hj,hjx⟩ := (show x ∈ (X' ⊔ Q').map f by rw [hcover]; trivial)
    refine ⟨⟨j.val,?_⟩,hjx⟩
    change j.val ∈ X ⊔ Q
    rw [← hJ]
    exact mem_map_of_mem _ hj
  have heker : φ.ker = (I ⊓ centralizer (E : Set G)).subgroupOf I := by
    ext i
    exact ⟨fun h => ⟨i.property,(planeAction_eq_one E (inclusion hIN i)).mp h⟩,
      fun h => (planeAction_eq_one E (inclusion hIN i)).mpr h.2⟩
  have hpker : IsPGroup 2 φ.ker := by rw [heker]; exact hkAmbient.comap_subtype
  have hcore := ker_eq_twoCore_of_surjective_perm_three φ hφ hpker
  refine ⟨?_,(normal_subgroupOf_iff_le_normalizer hXN).mp hnX,?_,?_⟩
  · have hh := congrArg (Subgroup.map N.subtype) he
    rw [map_conjugateSpanBy, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hQN, map_subgroupOf_eq_of_le hXN,
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  · change (pCore 2 I).map I.subtype = I ⊓ centralizer (E : Set G)
    rw [← hcore,heker,map_subgroupOf_eq_of_le inf_le_left]
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end CFSG.Quasithin.Chapter13.Section05.AmbientSource
