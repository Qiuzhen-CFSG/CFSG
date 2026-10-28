module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Elementary geometry and centralizers in the rank-three branch

For one already reselected source critical path, the preparation conclusions
put E = V₁ Zα inside the actual elementary abelian U. Distinct order-two
points give |E| = 4, while the prepared separation from V gives |V Zα| = 16.
If t in T moves E, its three-point span is exactly the original commutator
F = [U,Uα], with all three literal intersection containments preserved.

The original natural projection detects a point of Zα outside U₀. Its
stabilizer in the marked S₅ is a Sylow two-subgroup. Pullback through the
original qH proves C_G(E) = C_H(Zα) is a two-group. Earlier 14.5.15(1),
transported to the actual conjugate core, proves that Y_E and its embedded
two-residual normalize E; it also proves Y_E normalizes F.

`Preliminary` contains only conclusions explicitly assigned to
qt-14-07-rechoice-preparation. `CoreAxes` is an output contract for the
remaining restricted-pairing proof, not an earlier-source assumption or a
proved conclusion. Full action, relative normality, residual generation,
T-normalization and the actual L₁ span remain to be established and assembled
in RankThree. The order-six action on E alone does not give the required
order-twenty-four action on F.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.5.15(1), 14.7.64–65, and proof of 14.7.70, printed pp.1073–1074
(PDF pp.1090–1091). The source family uses O²(Y_E), not O₂(Y_E).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Exactly the preliminary conclusions supplied by the preparation branch,
for one and the same already reselected critical path. -/
structure Preliminary (d : Data T L V F W) (c : CriticalPath (L := L) F) : Prop where
  earlier : c.EarlierImages
  rank_three : primeRank 2 d.U₀ = 3
  star_card : Nat.card (star F c.Uα) = 2
  star_central : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G))
  commutator_le : Fcomm c ≤ F.U ⊓ c.Uα
  point_le : F.Vi 1 ≤ Fcomm c
  opposite_le : c.Zα ≤ Fcomm c
  commutator_normalized : (T : Subgroup G) ≤ normalizer (Fcomm c : Set G)
  commutator_card : Nat.card (Fcomm c) = 8
  commutator_inf : Fcomm c ⊓ d.U₀ = F.Vi 1
  opposite_not_le : ¬ c.Zα ≤ d.U₀
  disjoint_images : Disjoint (tilde d (Fcomm c)) (tilde d V)

/-- The actual three-point span considered when t moves E. -/
def movedSpan (c : CriticalPath (L := L) F) (t : G) : Subgroup G :=
  E c ⊔ conjugate c.Zα t

/-- Exact output contract for the restricted commutator-pairing branch.
Every automorphism fixing the indicated point and acting trivially modulo
it is realized by conjugation by the literal core. This is not supplied
as an earlier-source hypothesis to the final rank-three theorem. -/
def RealizesAxis (A P Q : Subgroup G) : Prop :=
  ∀ f : MulAut A,
    (∀ x : A, (f x : G) * (x : G)⁻¹ ∈ P) →
    (∀ x : A, (x : G) ∈ P → f x = x) →
    ∃ q ∈ Q, q ∈ normalizer (A : Set G) ∧
      ∀ x : A, q * (x : G) * q⁻¹ = (f x : G)

/-- The two independent full axis groups on the same original commutator.
The pairing producer must construct these; T-conjugation supplies the
third axis for a moved plane. -/
structure CoreAxes (c : CriticalPath (L := L) F) : Prop where
  original : RealizesAxis (Fcomm c) (F.Vi 1) (F.H.pCoreIn 2)
  reciprocal : RealizesAxis (Fcomm c) c.Zα c.Qα

variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

omit [Finite G] in
theorem opposite_card : Nat.card c.Zα = 2 := by
  change Nat.card ((F.Vi 1).map (MulAut.conj c.conjugator⁻¹).toMonoidHom) = 2
  rw [card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
  simpa using F.card 1 (by decide)

omit [Finite G] in
private theorem disjoint_of_card_two {A B : Subgroup G}
    (hB : Nat.card B = 2) (hn : ¬ B ≤ A) : Disjoint A B := by
  let : Fact (Nat.card B).Prime := ⟨hB ▸ Nat.prime_two⟩
  rcases (A.subgroupOf B).eq_bot_or_eq_top_of_prime_card with he | he
  · apply disjoint_iff.mpr
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hm : (⟨x, hx.2⟩ : B) ∈ A.subgroupOf B := hx.1
    rw [he] at hm
    exact congrArg Subtype.val (mem_bot.mp hm)
  · exact (hn (fun x hx => show (⟨x, hx⟩ : B) ∈ A.subgroupOf B by rw [he]; trivial)).elim

private theorem rank_of_card {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] {n : ℕ} (hc : Nat.card A = 2 ^ n) : primeRank 2 A = n := by
  apply le_antisymm (IsElementaryAbelian.primeRank_le_of_card_le A hc.le)
  exact (IsElementaryAbelian.rank_ge_of_card hc).trans
    (by
      rw [← Group.rank_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)]
      exact rank_le_primeRank_of_abelian_pGroup 2 (⊤ : Subgroup A)
        ((IsElementaryAbelian.isPGroup 2 A).of_injective (⊤ : Subgroup A).subtype
          (⊤ : Subgroup A).subtype_injective) inferInstance)

namespace Preliminary
variable {d c} (h : Preliminary d c)
include h

theorem E_le_commutator : E c ≤ Fcomm c := sup_le h.point_le h.opposite_le

theorem E_le_intersection : E c ≤ F.U ⊓ c.Uα :=
  h.E_le_commutator.trans h.commutator_le

theorem opposite_not_le_seed : ¬ c.Zα ≤ V :=
  point_not_le_seed d c h.earlier h.opposite_le h.opposite_not_le h.disjoint_images

theorem opposite_disjoint_point : Disjoint (F.Vi 1) c.Zα :=
  disjoint_of_card_two (opposite_card c) (fun hn => h.opposite_not_le (hn.trans d.point_le_U₀))

theorem opposite_disjoint_seed : Disjoint V c.Zα :=
  disjoint_of_card_two (opposite_card c) h.opposite_not_le_seed

theorem E_elementary : IsElementaryAbelian 2 (E c) := by
  let := d.U_elementary
  exact IsElementaryAbelian.of_le (h.E_le_intersection.trans inf_le_left)

omit h in
include d in
private theorem subgroups_commute {A B : Subgroup G} (hA : A ≤ F.U) (hB : B ≤ F.U) :
    B ≤ centralizer (A : Set G) := by
  let : IsMulCommutative F.U := d.abelian
  intro b hb a ha
  exact congrArg Subtype.val (mul_comm (⟨a, hA ha⟩ : F.U) ⟨b, hB hb⟩)

theorem E_card : Nat.card (E c) = 4 := by
  have hcomm := subgroups_commute (d := d) d.conjugationSection.kernel_le
    (h.opposite_le.trans (h.commutator_le.trans inf_le_left))
  change Nat.card (↥(F.Vi 1 ⊔ c.Zα)) = 4
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hcomm.trans (Subgroup.centralizer_le_normalizer _)) h.opposite_disjoint_point,
    opposite_card c, F.card 1 (by decide)]
  decide

theorem E_rank : primeRank 2 (E c) = 2 := by
  let := h.E_elementary
  exact rank_of_card h.E_card

theorem seed_sup_opposite_elementary : IsElementaryAbelian 2 (↥(V ⊔ c.Zα)) := by
  let := d.U_elementary
  exact IsElementaryAbelian.of_le (sup_le (Data.V_le_U F)
    (h.opposite_le.trans (h.commutator_le.trans inf_le_left)))

theorem seed_sup_opposite_card : Nat.card (↥(V ⊔ c.Zα)) = 16 := by
  have hcomm := subgroups_commute (d := d) (Data.V_le_U F)
    (h.opposite_le.trans (h.commutator_le.trans inf_le_left))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hcomm.trans (Subgroup.centralizer_le_normalizer _)) h.opposite_disjoint_seed,
    opposite_card c, ← F.last, F.card 3 (by decide)]
  decide

theorem seed_sup_opposite_rank : primeRank 2 (↥(V ⊔ c.Zα)) = 4 := by
  let := h.seed_sup_opposite_elementary
  exact rank_of_card h.seed_sup_opposite_card


/-- T-normalization of the original commutator gives the third literal
intersection, with the project's right-conjugation convention. -/
theorem commutator_le_opposite_conjugate (t : G) (ht : t ∈ (T : Subgroup G)) :
    Fcomm c ≤ conjugate c.Uα t := by
  calc
    Fcomm c = conjugate (Fcomm c) t :=
      ((conjugate_eq_iff _ _).mpr (h.commutator_normalized ht)).symm
    _ ≤ conjugate c.Uα t := map_mono (h.commutator_le.trans inf_le_right)

/-- A moved E gives all of the original rank-three commutator, rather than
an unrelated abstract vector space of the same dimension. -/
theorem moved_span_eq_commutator (t : G) (ht : t ∈ (T : Subgroup G))
    (hm : t ∉ normalizer (E c : Set G)) : movedSpan c t = Fcomm c := by
  have hP : conjugate (F.Vi 1) t = F.Vi 1 :=
    (conjugate_eq_iff _ _).mpr (F.invariant 1 ht)
  have hZ : conjugate c.Zα t ≤ Fcomm c :=
    (map_mono h.opposite_le).trans_eq
      ((conjugate_eq_iff _ _).mpr (h.commutator_normalized ht))
  have hnot : ¬ conjugate c.Zα t ≤ E c := by
    intro hz
    have he : conjugate (E c) t ≤ E c := by
      change (F.Vi 1 ⊔ c.Zα).map (MulAut.conj t⁻¹).toMonoidHom ≤ _
      rw [Subgroup.map_sup]
      exact sup_le (hP.le.trans le_sup_left) hz
    have heq : conjugate (E c) t = E c := eq_of_le_of_card_ge he (by
      change Nat.card (E c) ≤ Nat.card ((E c).map (MulAut.conj t⁻¹).toMonoidHom)
      rw [card_map_of_injective (MulAut.conj t⁻¹).injective])
    exact hm ((conjugate_eq_iff _ _).mp heq)
  have hzcard : Nat.card (conjugate c.Zα t) = 2 := by
    change Nat.card (c.Zα.map (MulAut.conj t⁻¹).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj t⁻¹).injective, opposite_card c]
  have hcomm := subgroups_commute (d := d)
    (h.E_le_intersection.trans inf_le_left) (hZ.trans (h.commutator_le.trans inf_le_left))
  have hcard : Nat.card (movedSpan c t) = 8 := by
    rw [movedSpan, card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hcomm.trans (Subgroup.centralizer_le_normalizer _))
      (disjoint_of_card_two hzcard hnot), h.E_card, hzcard]
  exact eq_of_le_of_card_ge (sup_le h.E_le_commutator hZ)
    (by rw [hcard, h.commutator_card])

theorem moved_span_rank (t : G) (ht : t ∈ (T : Subgroup G))
    (hm : t ∉ normalizer (E c : Set G)) : primeRank 2 (movedSpan c t) = 3 := by
  rw [h.moved_span_eq_commutator t ht hm]
  let := d.U_elementary
  let : IsElementaryAbelian 2 (Fcomm c) :=
    IsElementaryAbelian.of_le (h.commutator_le.trans inf_le_left)
  exact rank_of_card h.commutator_card

end Preliminary

include d in
/-- The literal point centralizer is H, not merely a subgroup containing H. -/
theorem point_centralizer : centralizer (F.Vi 1 : Set G) = F.H := by
  rw [d.point, zpowers_eq_closure, centralizer_closure, ← d.centralizer_eq]

include d in
/-- The centralizer needed in the source is exactly C_H(Zα). -/
theorem E_centralizer : centralizer (E c : Set G) = F.H ⊓ centralizer (c.Zα : Set G) := by
  change centralizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) = _
  rw [← point_centralizer d]
  apply le_antisymm
  · exact le_inf (centralizer_le (show F.Vi 1 ≤ F.Vi 1 ⊔ c.Zα from le_sup_left))
      (centralizer_le (show c.Zα ≤ F.Vi 1 ⊔ c.Zα from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (inf_le_left :
      centralizer (F.Vi 1 : Set G) ⊓ centralizer (c.Zα : Set G) ≤ _))
      (le_centralizer_iff.mp (inf_le_right :
      centralizer (F.Vi 1 : Set G) ⊓ centralizer (c.Zα : Set G) ≤ _))

/-- The original natural quotient detects every point outside U₀. Its
nonzero-vector stabilizer is a Sylow two-subgroup of the same marked S₅. -/
theorem centralizer_two_of_outside (a : F.U) (ha : (a : G) ∉ d.U₀) :
    IsPGroup 2 (↥(F.H ⊓ centralizer ({(a : G)} : Set G))) := by
  let v := d.projection (d.conjugationSection.coordinates a).toAdd
  have hv : v ≠ 0 := by
    intro hz
    exact ha ((d.mem_U₀ a).mpr hz)
  let P := naturalPointSylow d.naturalQuotient v hv
  have hker : IsPGroup 2 d.qH.ker := by
    rw [d.qH_ker]
    exact (isPGroup_pCoreIn 2 F.H).comap_subtype
  have hP : IsPGroup 2 ((P : Subgroup ChapterJ.S5).comap d.qH) :=
    P.isPGroup'.comap_of_ker_isPGroup d.qH hker
  let C := F.H ⊓ centralizer ({(a : G)} : Set G)
  let f : C →* ((P : Subgroup ChapterJ.S5).comap d.qH) := {
    toFun x := ⟨⟨x, x.property.1⟩, by
      change d.naturalQuotient.action (d.qH ⟨x, x.property.1⟩) v = v
      have hax : (x : G) * a * (x : G)⁻¹ = a := by
        rw [mem_centralizer_singleton_iff.mp x.property.2, mul_inv_cancel_right]
      have he : d.action ⟨x, x.property.1⟩ (d.conjugationSection.coordinates a).toAdd =
          (d.conjugationSection.coordinates a).toAdd :=
        (d.conjugationSection.equivariant ⟨x, x.property.1⟩ a).symm.trans
          (congrArg (fun b : F.U => (d.conjugationSection.coordinates b).toAdd) (Subtype.ext hax))
      exact (LinearMap.congr_fun (d.projection.isIntertwining' ⟨x, x.property.1⟩) _).symm.trans
        (congrArg d.projection he)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  exact hP.of_injective f (fun _ _ he => Subtype.ext (congrArg (fun x => (x.val : G)) he))

namespace Preliminary
variable {d c} (h : Preliminary d c)
include h

/-- This derives the two-group centralizer without an A.1.14 premise. -/
theorem E_centralizer_two : IsPGroup 2 (centralizer (E c : Set G)) := by
  have hex : ∃ a ∈ c.Zα, a ∉ d.U₀ := by
    by_contra! he
    exact h.opposite_not_le he
  obtain ⟨a, ha, hn⟩ := hex
  have hU := h.opposite_le.trans (h.commutator_le.trans inf_le_left)
  have hp := centralizer_two_of_outside d ⟨a, hU ha⟩ hn
  rw [E_centralizer d c]
  exact hp.of_injective (inclusion
    (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ha))))
      (inclusion_injective _)


/-- Original 14.5.15(1) and its conjugate already give normalization.
No nontrivial commutator or full-action assertion is needed here. -/
theorem YE_normalizes (h15 : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1) :
    YE c ≤ normalizer (E c : Set G) := by
  have hα : ⁅c.Uα, c.Qα⁆ ≤ c.Zα := by
    have hm := map_mono (f := (MulAut.conj c.conjugator⁻¹).toMonoidHom) h15
    rw [map_commutator,
      map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective] at hm
    exact hm
  apply sup_le
  · exact le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono (h.E_le_intersection.trans inf_le_left) le_rfl).trans
        (h15.trans le_sup_left))
  · exact le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono (h.E_le_intersection.trans inf_le_right) le_rfl).trans
        (hα.trans le_sup_right))

/-- The literal two vertex cores also preserve the whole commutator,
which is the carrier of the subsequent three-axis argument. -/
theorem YE_normalizes_commutator (h15 : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1) :
    YE c ≤ normalizer (Fcomm c : Set G) := by
  have hα : ⁅c.Uα, c.Qα⁆ ≤ c.Zα := by
    have hm := map_mono (f := (MulAut.conj c.conjugator⁻¹).toMonoidHom) h15
    rw [map_commutator,
      map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective] at hm
    exact hm
  apply sup_le
  · exact le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono (h.commutator_le.trans inf_le_left) le_rfl).trans
        (h15.trans h.point_le))
  · exact le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono (h.commutator_le.trans inf_le_right) le_rfl).trans
        (hα.trans h.opposite_le))

/-- The same normalization holds for the literal embedded two-residual. -/
theorem Y_normalizes (h15 : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1) :
    Y c ≤ normalizer (E c : Set G) :=
  (map_subtype_le (pResidual 2 (YE c))).trans (h.YE_normalizes h15)

/-- Consequently the actual residual orbit-span is contained in E.
The reverse inclusion still requires the nontrivial residual action. -/
theorem residual_span_le (h15 : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1) :
    conjugateSpanBy (F.Vi 1) (Y c) ≤ E c :=
  conjugateSpanBy_le le_sup_left (h.Y_normalizes h15)


/-- Once the actual L₁ span is identified, its order sixteen rules out
normalization of E. This is only the final cardinal comparison; the span
identity must be supplied by the independent original-action calculation. -/
theorem L₁_not_normalizes_of_span
    (hs : conjugateSpanBy c.Zα (F.Li L 1) = V ⊔ c.Zα) :
    ¬ F.Li L 1 ≤ normalizer (E c : Set G) := by
  intro hn
  have hle : V ⊔ c.Zα ≤ E c := hs ▸
    conjugateSpanBy_le (le_sup_right : c.Zα ≤ E c) hn
  have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rw [h.seed_sup_opposite_card, h.E_card] at hc
  omega

end Preliminary
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
