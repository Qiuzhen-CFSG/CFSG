module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowQuotient
public import Theory.GroupTheory.PResidual.PrimeActorImage
/-!
# Faithful prime actors in the changed-Sylow quotient

At the smaller changed Sylow T₀, the two-core of each overgroup X
normalizes the perfect right factor. Normalizer reflection through this
kernel shows that the actual order-three or order-five actor still has
order p in X/O₂(X) and meets the factor's normalizer trivially. Thus its
p conjugates are distinct and its action on every normalized containing
component image is faithful. The original Cartan Borel also proves that
the literal subgroup DT₀ is solvable.

The final theorem applies these facts to the proper normal component
already constructed in G₀T₀, retaining the concrete quotient map, the
Bender-model exclusion, and the alternative where the changed subgroup
is an ambient Sylow. The model sieve and larger-Sylow exclusion remain
with qt-d-1222-rankone-cartan-local-to-global, which also owns the final
normalization assembly; no additional model premise is discharged here.

Source: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636 and 648--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] : IsPPerfect 2 Y := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (Y ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (Y ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (Y ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (Y ⧸ N) inferInstance

omit [Finite G] in
/-- The literal two-core kernel normalizes the right factor at the small Sylow. -/
theorem right_core_normalizes
    {T : Sylow 2 G} {R X : Subgroup G}
    (hRX : R ≤ X) (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X) :
    pCore 2 X ≤ normalizer (R.subgroupOf X : Set X) := by
  obtain ⟨P,hP⟩ := hSyl
  rw [← subgroupOf_normalizer_eq hRX]
  intro x hx
  have hc : X.pCoreIn 2 ≤ normalizingSylow T R := hP ▸ pCoreIn_le_sylow X P
  exact (hc (mem_map_of_mem X.subtype hx)).2

/-- The source quotient reflects the normalizer of the right factor exactly. -/
theorem LocalData.right_quotient_normalizer
    {T : Sylow 2 G} {L W H B D R X : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hRX : R ≤ X) (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X) :
    let q := QuotientGroup.mk' (pCore 2 X)
    (normalizer ((R.subgroupOf X).map q : Set (X ⧸ pCore 2 X))).comap q =
      (normalizer (R : Set G)).subgroupOf X := by
  obtain ⟨P,hP⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hP ▸ map_subtype_le (P : Subgroup X)
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  let := Chapter1.mem_L_isPerfect hlocal
  dsimp only
  rw [comap_normalizer_map_of_pPerfect (QuotientGroup.mk' (pCore 2 X))
    (R.subgroupOf X) perfect_twoPerfect
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (by simpa only [QuotientGroup.ker_mk'] using right_core_normalizes hRX ⟨P,hP⟩)]
  exact (subgroupOf_normalizer_eq hRX).symm

/-- The same prime actor has order p and no nonidentity normalizer elements
in the literal quotient. Its p conjugates of the right factor are distinct. -/
theorem LocalData.right_quotient_prime_orbit
    {T : Sylow 2 G} {L W H A B D R X : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hRX : R ≤ X) (hDX : D ≤ X)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X) :
    let q := QuotientGroup.mk' (pCore 2 X)
    let Rbar := (R.subgroupOf X).map q
    let Dbar := (D.subgroupOf X).map q
    Nat.card Dbar = p ∧ Disjoint Dbar (normalizer (Rbar : Set (X ⧸ pCore 2 X))) ∧
      Function.Injective (fun a : Dbar => Rbar.conjBy (a : X ⧸ pCore 2 X)) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨P,hP⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hP ▸ map_subtype_le (P : Subgroup X)
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  let := Chapter1.mem_L_isPerfect hlocal
  have hmove : ¬ D.subgroupOf X ≤ normalizer (R.subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hRX]
    intro hnorm
    apply d.prime_actor_not_normalizes_right h hH c hd hz
    intro x hx
    exact hnorm (show (⟨x,hDX hx⟩ : X) ∈ D.subgroupOf X from hx)
  have hcard : Nat.card (D.subgroupOf X) = p :=
    (Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv).trans hd.card
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  obtain ⟨hc,hdj⟩ := prime_actor_image_disjoint_normalizer q (R.subgroupOf X)
    (D.subgroupOf X) perfect_twoPerfect
    (by dsimp only [q]; rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (by simpa only [q, QuotientGroup.ker_mk'] using right_core_normalizes hRX ⟨P,hP⟩)
    (hcard ▸ hp) hmove
  exact ⟨hc.trans hcard,hdj,conjugates_injective_of_disjoint_normalizer hdj⟩

/-- The actual prime actor and T₀ generate a solvable subgroup. The prime
actor normalizes U=T∩L, and T₀ normalizes the characteristic preimage UD
in the cyclic Cartan quotient of the original Borel. -/
theorem LocalData.actor_join_solvable
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    Group.IsSolvable (D ⊔ normalizingSylow T R : Subgroup G) := by
  let U := (T : Subgroup G) ⊓ L
  let T₀ := normalizingSylow T R
  have hUT₀ : U ≤ T₀ := by
    dsimp only [U]
    rw [← d.S_intersection_left]
    exact inf_le_left.trans (d.sourceS_le_normalizingSylow h hH)
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hTBorel : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes
      (hTU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hT₀UD : T₀ ≤ normalizer ((U ⊔ D : Subgroup G) : Set G) :=
    (inf_le_left.trans hTBorel).trans
      (cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear hd.le_cartan)
  have hDU : D ≤ normalizer (U : Set G) :=
    hd.le_cartan.trans (c.left_le.trans inf_le_right)
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hd.card
  let : Group.IsNilpotent U := (T.isPGroup'.to_le (show U ≤ (T : Subgroup G) from inf_le_left)).isNilpotent
  let : Group.IsNilpotent T₀ := (T.isPGroup'.to_le (show T₀ ≤ (T : Subgroup G) from inf_le_left)).isNilpotent
  let : Group.IsSolvable (U ⊔ D : Subgroup G) := Group.isSolvable_sup_of_normalizes U D hDU
  have hs := Group.isSolvable_sup_of_normalizes (U ⊔ D) T₀ hT₀UD
  have he : (U ⊔ D) ⊔ T₀ = D ⊔ T₀ := by
    rw [sup_assoc, sup_eq_right.mpr (hUT₀.trans le_sup_right)]
  exact he ▸ hs

/-- The chosen containing component carries a faithful action of the actual
order-p image. All normality is relative to the source group X. -/
theorem LocalData.source_overcomponent_prime_action
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R)) :
    let X := generated L H D R ⊔ normalizingSylow T R
    let q := QuotientGroup.mk' (pCore 2 X)
    let Rbar := (R.subgroupOf X).map q
    let Dbar := (D.subgroupOf X).map q
    ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
      (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
      Rbar < (K.subgroupOf X).map q ∧
      ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
      Nat.card Dbar = p ∧ Disjoint Dbar (normalizer (Rbar : Set (X ⧸ pCore 2 X))) ∧
      Function.Injective (fun a : Dbar => Rbar.conjBy (a : X ⧸ pCore 2 X)) ∧
      ∃ hn : Dbar ≤ normalizer (((K.subgroupOf X).map q) : Set (X ⧸ pCore 2 X)),
        Function.Injective (((K.subgroupOf X).map q).normalizerMonoidHom.comp (inclusion hn)) := by
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨K,hRK,hKX,hK,hKn,hlt,hmodel⟩ := d.source_overcomponent_nonBender h hH c hd hz hSyl
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  obtain ⟨hcard,hdis,horbit⟩ := d.right_quotient_prime_orbit h hH c hd hz hRX hDX hSyl
  let : (K.subgroupOf X).Normal := hKn
  have hn : (D.subgroupOf X).map q ≤ normalizer (((K.subgroupOf X).map q) : Set (X ⧸ pCore 2 X)) :=
    (map_mono (f := q) (show D.subgroupOf X ≤ normalizer (K.subgroupOf X : Set X)
      from le_normalizer_of_normal)).trans (le_normalizer_map q)
  exact ⟨K,hRK,hKX,hK,hKn,hlt,hmodel,hcard,hdis,horbit,hn,
    normalizer_action_injective_of_disjoint_normalizer hlt.le hn hdis⟩

/-- The changed Sylow retains its action on DT₀ and, in the small branch,
the faithful prime action on the proper quotient overcomponent. -/
theorem LocalData.changedSylow_prime_action
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      Group.IsSolvable (D ⊔ normalizingSylow T R : Subgroup G) ∧
      normalizingSylow T R ≤ T₁ ∧
      T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
      ((T₁ = normalizingSylow T R ∧
        let X := generated L H D R ⊔ normalizingSylow T R
        let q := QuotientGroup.mk' (pCore 2 X)
        let Rbar := (R.subgroupOf X).map q
        let Dbar := (D.subgroupOf X).map q
        ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          Rbar < (K.subgroupOf X).map q ∧
          ¬ ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∧
          Nat.card Dbar = p ∧ Disjoint Dbar (normalizer (Rbar : Set (X ⧸ pCore 2 X))) ∧
          Function.Injective (fun a : Dbar => Rbar.conjBy (a : X ⧸ pCore 2 X)) ∧
          ∃ hn : Dbar ≤ normalizer (((K.subgroupOf X).map q) : Set (X ⧸ pCore 2 X)),
            Function.Injective (((K.subgroupOf X).map q).normalizerMonoidHom.comp (inclusion hn))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨_,_,P,hTP,_,hD,_,hcases⟩ := d.changedSylow_action h hH c hd hz
  refine ⟨P,d.actor_join_solvable h hH c hd,hTP,hD,?_⟩
  rcases hcases with he | ha
  · have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
        (generated L H D R ⊔ normalizingSylow T R) :=
      (Chapter1.IsSylowIn.restrict ⟨P,he⟩ le_sup_right le_sup_left)
    exact Or.inl ⟨he,d.source_overcomponent_prime_action h hH c hd hz hSyl⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
