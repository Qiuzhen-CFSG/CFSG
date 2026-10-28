module

public import Theory.GroupTheory.PResidual.SubnormalCorePreimage
public import Theory.GroupTheory.PResidual.OddImage
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupAction.ElementaryNineSylowLine
public import Theory.GroupTheory.CubicAutomorphismLines
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Normal cubic residuals and the four lines of an elementary nine quotient

For a finite group X with elementary abelian quotient X/O₂(X) of order nine,
normal two-perfect subgroups Y with |Y/O₂(Y)| = 3 correspond to its four
cubic lines. The forward map is the literal quotient image; the inverse
is the embedded two-residual of the line preimage. Subnormal core
intersection and residual recovery prove the two inverse identities.

The correspondence respects automorphisms and ambient normalizer
conjugation. An actor fixing one marked quotient line and inverting a
distinct one has exactly those possibilities for an invariant normal cubic
residual. All normality in the ambient family is relative to X.

Source application: Aschbacher–Smith, 12.4.6, printed p.814. The normality
condition repairs the counting step for the unrestricted printed family;
it does not change the existing unrestricted-family interfaces.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.NormalCubicLines
variable {X : Type*} [Group X] [Finite X]

/-- Intrinsic normal two-perfect subgroups with cubic two-core quotient. -/
def family (X : Type*) [Group X] : Set (Subgroup X) :=
  {Y | Y.Normal ∧ IsPPerfect 2 Y ∧ Nat.card (Y ⧸ pCore 2 Y) = 3}

/-- Image under the literal quotient map X → X/O₂(X). -/
def image (Y : Subgroup X) : Subgroup (X ⧸ pCore 2 X) :=
  Y.map (QuotientGroup.mk' (pCore 2 X))

/-- The embedded two-residual of the full quotient-line preimage. -/
def lift (A : Subgroup (X ⧸ pCore 2 X)) : Subgroup X :=
  (pResidual 2 (A.comap (QuotientGroup.mk' (pCore 2 X)))).map
    (A.comap (QuotientGroup.mk' (pCore 2 X))).subtype

/-- Subnormal core intersection identifies the intrinsic core quotient with its actual image. -/
noncomputable def coreQuotientEquivImage (Y : Subgroup X) (hn : Y.IsSubnormal) :
    (Y ⧸ pCore 2 Y) ≃* image Y := by
  let f := (QuotientGroup.mk' (pCore 2 X)).subgroupMap Y
  have he : f.ker = pCore 2 Y := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hn).symm
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 X)).subgroupMap_surjective Y))

theorem image_card (Y : Subgroup X) (hY : Y ∈ family X) :
    Nat.card (image Y) = 3 :=
  (Nat.card_congr (coreQuotientEquivImage Y hY.1.isSubnormal).toEquiv).symm.trans hY.2.2

omit [Finite X] in
/-- Subnormal two-perfect subgroups are recovered from their quotient images. -/
theorem lift_image (Y : Subgroup X) (hn : Y.IsSubnormal) (hp : IsPPerfect 2 Y) :
    lift (image Y) = Y := residual_core_preimage_eq Y hn hp

omit [Finite X] in
theorem image_injective {Y Z : Subgroup X} (hY : Y ∈ family X) (hZ : Z ∈ family X)
    (he : image Y = image Z) : Y = Z := by
  rw [← lift_image Y hY.1.isSubnormal hY.2.1,
    ← lift_image Z hZ.1.isSubnormal hZ.2.1, he]

/-- Taking the residual of a line preimage retains the whole odd image. -/
theorem image_lift (hX : Odd (Nat.card (X ⧸ pCore 2 X)))
    (A : Subgroup (X ⧸ pCore 2 X)) : image (lift A) = A := by
  dsimp only [image, lift]
  rw [embedded_twoResidual_map_eq_of_odd _ hX,
    map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)]

theorem lift_mem [IsElementaryAbelian 3 (X ⧸ pCore 2 X)]
    (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (A : Subgroup (X ⧸ pCore 2 X)) (hA : Nat.card A = 3) : lift A ∈ family X := by
  have hn : (lift A).Normal := by dsimp only [lift]; infer_instance
  refine ⟨hn, isPPerfect_embedded_pResidual 2 _, ?_⟩
  rw [Nat.card_congr (coreQuotientEquivImage (lift A) hn.isSubnormal).toEquiv,
    image_lift (by rw [hX]; decide), hA]

/-- The quotient-image bijection, with residual-preimage inverse. -/
noncomputable def equivLines [IsElementaryAbelian 3 (X ⧸ pCore 2 X)]
    (hX : Nat.card (X ⧸ pCore 2 X) = 9) :
    family X ≃ {A : Subgroup (X ⧸ pCore 2 X) // Nat.card A = 3} where
  toFun Y := ⟨image Y.val, image_card Y.val Y.property⟩
  invFun A := ⟨lift A.val, lift_mem hX A.val A.property⟩
  left_inv Y := Subtype.ext (lift_image Y.val Y.property.1.isSubnormal Y.property.2.1)
  right_inv A := Subtype.ext (image_lift (by rw [hX]; decide) A.val)

/-- The intrinsic normal cubic family has exactly four members. -/
theorem ncard_family [IsElementaryAbelian 3 (X ⧸ pCore 2 X)]
    (hX : Nat.card (X ⧸ pCore 2 X) = 9) : (family X).ncard = 4 := by
  change Nat.card (family X) = 4
  exact (Nat.card_congr (equivLines hX)).trans
    (IsElementaryAbelian.TernarySylowLine.card_cubic_subgroups hX)

omit [Finite X] in
theorem map_mem (a : MulAut X) (Y : Subgroup X) (hY : Y ∈ family X) :
    Y.map a.toMonoidHom ∈ family X := by
  let e := a.subgroupMap Y
  refine ⟨hY.1.map _ a.surjective,
    hY.2.1.of_surjective e.toMonoidHom e.surjective, ?_⟩
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hY.2.2

omit [Finite X] in
/-- Literal quotient images intertwine the original and induced automorphisms. -/
theorem image_map (a : MulAut X) (Y : Subgroup X) :
    image (Y.map a.toMonoidHom) =
      (image Y).map ((pCore 2 X).quotientAut a).toMonoidHom := by
  dsimp only [image]
  rw [map_map, map_map]
  congr 1
  ext x
  exact (quotientAut_apply_mk _ a x).symm

/-- The inverse correspondence is equivariant as well. -/
theorem lift_map [IsElementaryAbelian 3 (X ⧸ pCore 2 X)]
    (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (a : MulAut X) (A : Subgroup (X ⧸ pCore 2 X)) (hA : Nat.card A = 3) :
    lift (A.map ((pCore 2 X).quotientAut a).toMonoidHom) =
      (lift A).map a.toMonoidHom := by
  have hodd : Odd (Nat.card (X ⧸ pCore 2 X)) := by rw [hX]; decide
  apply image_injective (lift_mem hX _ ((card_map_of_injective
    ((pCore 2 X).quotientAut a).injective).trans hA)) (map_mem a _ (lift_mem hX A hA))
  rw [image_lift hodd, image_map, image_lift hodd]

/-- Two different cubic lines in a group of order nine span the group. -/
theorem cubic_sup_eq_top {E : Type*} [CommGroup E] [Finite E]
    (hE : Nat.card E = 9) (A B : Subgroup E)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hne : A ≠ B) : A ⊔ B = ⊤ := by
  let : Fact (Nat.card A).Prime := ⟨hA ▸ Nat.prime_three⟩
  have hdis : Disjoint A B := by
    rcases (B.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply disjoint_iff.mpr
      have hm := congrArg (map A.subtype) hb
      simpa only [subgroupOf_map_subtype, Subgroup.map_bot, inf_comm] using hm
    · have hle : A ≤ B := by
        intro a ha
        exact (show (⟨a, ha⟩ : A) ∈ B.subgroupOf A from ht.symm ▸ mem_top _)
      exact (hne (eq_of_le_of_card_ge hle (by omega))).elim
  apply eq_top_of_card_eq
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A B (by rw [normalizer_eq_top]; exact le_top)
    hdis, hA, hB, hE]

/-- The two marked quotient directions exhaust invariant cubic residuals. -/
theorem invariant_eq_marked [IsElementaryAbelian 3 (X ⧸ pCore 2 X)]
    (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (A B Y : Subgroup X) (hA : A ∈ family X) (hB : B ∈ family X)
    (hY : Y ∈ family X) (hne : image A ≠ image B) (a : MulAut X)
    (hfix : ∀ z ∈ image A, (pCore 2 X).quotientAut a z = z)
    (hinv : ∀ z ∈ image B, (pCore 2 X).quotientAut a z = z⁻¹)
    (hstable : Y.map a.toMonoidHom = Y) : Y = A ∨ Y = B := by
  have hs : ∀ z ∈ image Y, (pCore 2 X).quotientAut a z ∈ image Y := by
    intro z hz
    have hh := mem_map_of_mem ((pCore 2 X).quotientAut a).toMonoidHom hz
    rwa [← image_map, hstable] at hh
  exact (CubicAutomorphismLines.invariant_line_eq (image A) (image B) (image Y)
    (image_card A hA) (image_card B hB) (image_card Y hY)
    (cubic_sup_eq_top hX _ _ (image_card A hA) (image_card B hB) hne)
    ((pCore 2 X).quotientAut a) hfix hinv hs).imp
    (image_injective hY hA) (image_injective hY hB)

end Theory.GroupTheory.NormalCubicLines

namespace Subgroup
open Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The normal two-perfect cubic residuals inside an ambient subgroup. -/
def normalCubicResiduals (X : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≤ X ∧ (Y.subgroupOf X).Normal ∧ IsPPerfect 2 Y ∧
    Nat.card (Y ⧸ pCore 2 Y) = 3}

theorem mem_normalCubicResiduals_iff (X Y : Subgroup G) (hle : Y ≤ X) :
    Y ∈ normalCubicResiduals X ↔ Y.subgroupOf X ∈ NormalCubicLines.family X := by
  let e := subgroupOfEquivOfLe hle
  have hc := Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv
  constructor
  · rintro ⟨_, hn, hp, hcard⟩
    exact ⟨hn, hp.of_surjective e.symm.toMonoidHom e.symm.surjective, hc.trans hcard⟩
  · rintro ⟨hn, hp, hcard⟩
    exact ⟨hle, hn, hp.of_surjective e.toMonoidHom e.surjective, hc.symm.trans hcard⟩

theorem normalCubicResiduals_map_subtype (X : Subgroup G) (Y : Subgroup X)
    (hY : Y ∈ NormalCubicLines.family X) : Y.map X.subtype ∈ normalCubicResiduals X := by
  apply (mem_normalCubicResiduals_iff X _ (map_subtype_le _)).mpr
  have he : (Y.map X.subtype).subgroupOf X = Y := by
    exact comap_map_eq_self_of_injective X.subtype_injective Y
  rwa [he]

/-- Passing between ambient subgroups and subgroups of X preserves the normal family. -/
noncomputable def normalCubicResidualsEquiv (X : Subgroup G) :
    normalCubicResiduals X ≃ NormalCubicLines.family X where
  toFun Y := ⟨Y.val.subgroupOf X, (mem_normalCubicResiduals_iff X Y.val Y.property.1).mp Y.property⟩
  invFun Y := ⟨Y.val.map X.subtype, normalCubicResiduals_map_subtype X Y.val Y.property⟩
  left_inv Y := Subtype.ext (map_subgroupOf_eq_of_le Y.property.1)
  right_inv Y := Subtype.ext (comap_map_eq_self_of_injective X.subtype_injective Y.val)

/-- The actual ambient family also has exactly four members. -/
theorem normalCubicResiduals_ncard [Finite G] (X : Subgroup G)
    [IsElementaryAbelian 3 (X ⧸ pCore 2 X)] (hX : Nat.card (X ⧸ pCore 2 X) = 9) :
    (normalCubicResiduals X).ncard = 4 := by
  exact (Nat.card_congr (normalCubicResidualsEquiv X)).trans
    (NormalCubicLines.ncard_family hX)

/-- Conjugation by N_G(X) preserves the relative-normal cubic family. -/
theorem normalCubicResiduals_conjugate (X Y : Subgroup G) (g : G)
    (hg : g ∈ normalizer (X : Set G)) (hY : Y ∈ normalCubicResiduals X) :
    Y.map (MulAut.conj g).toMonoidHom ∈ normalCubicResiduals X := by
  let e := (MulAut.conj g).subgroupMap Y
  have hle : Y.map (MulAut.conj g).toMonoidHom ≤ X :=
    (map_mono hY.1).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)
  refine ⟨hle, (normal_subgroupOf_iff_le_normalizer hle).mpr ?_,
    hY.2.2.1.of_surjective e.toMonoidHom e.surjective, ?_⟩
  · rw [← mem_normalizer_iff_map_conj_eq.mp hg]
    exact (map_mono ((normal_subgroupOf_iff_le_normalizer hY.1).mp hY.2.1)).trans
      (Y.le_normalizer_map (MulAut.conj g).toMonoidHom)
  · exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hY.2.2.2

/-- The line uses the subgroup inclusion into X and its literal two-core quotient. -/
def normalCubicResidualImage (X Y : Subgroup G) : Subgroup (X ⧸ pCore 2 X) :=
  NormalCubicLines.image (Y.subgroupOf X)

theorem normalCubicResidualImage_injective {X Y Z : Subgroup G}
    (hY : Y ∈ normalCubicResiduals X) (hZ : Z ∈ normalCubicResiduals X)
    (he : normalCubicResidualImage X Y = normalCubicResidualImage X Z) : Y = Z := by
  have hi := NormalCubicLines.image_injective
    ((mem_normalCubicResiduals_iff X Y hY.1).mp hY)
    ((mem_normalCubicResiduals_iff X Z hZ.1).mp hZ) he
  have hm := congrArg (map X.subtype) hi
  simpa only [map_subgroupOf_eq_of_le hY.1, map_subgroupOf_eq_of_le hZ.1] using hm

/-- The actual quotient action of N_G(X). -/
def normalCubicQuotientAction (X : Subgroup G) :
    normalizer (X : Set G) →* MulAut (X ⧸ pCore 2 X) :=
  (pCore 2 X).quotientAut.comp X.normalizerMonoidHom

theorem normalCubicResidual_subgroupOf_conjugate (X Y : Subgroup G) (hle : Y ≤ X)
    (g : normalizer (X : Set G)) :
    (Y.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf X =
      (Y.subgroupOf X).map (X.normalizerMonoidHom g).toMonoidHom := by
  apply map_injective X.subtype_injective
  have hm : X.subtype.comp (X.normalizerMonoidHom g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp X.subtype := by ext x; rfl
  rw [map_map, hm, ← map_map, map_subgroupOf_eq_of_le hle]
  exact map_subgroupOf_eq_of_le ((map_mono hle).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp g.property))

theorem normalCubicResidualImage_conjugate (X Y : Subgroup G) (hle : Y ≤ X)
    (g : normalizer (X : Set G)) :
    normalCubicResidualImage X (Y.map (MulAut.conj (g : G)).toMonoidHom) =
      (normalCubicResidualImage X Y).map (normalCubicQuotientAction X g).toMonoidHom := by
  unfold normalCubicResidualImage
  rw [normalCubicResidual_subgroupOf_conjugate X Y hle, NormalCubicLines.image_map]
  rfl

theorem normalCubicResidualImage_card [Finite G] {X Y : Subgroup G}
    (hY : Y ∈ normalCubicResiduals X) : Nat.card (normalCubicResidualImage X Y) = 3 :=
  NormalCubicLines.image_card _ ((mem_normalCubicResiduals_iff X Y hY.1).mp hY)

/-- The ambient correspondence still uses the literal quotient map on X. -/
noncomputable def normalCubicResidualsEquivLines [Finite G] (X : Subgroup G)
    [IsElementaryAbelian 3 (X ⧸ pCore 2 X)] (hX : Nat.card (X ⧸ pCore 2 X) = 9) :
    normalCubicResiduals X ≃ {A : Subgroup (X ⧸ pCore 2 X) // Nat.card A = 3} :=
  (normalCubicResidualsEquiv X).trans (NormalCubicLines.equivLines hX)

/-- The two quotient eigenspaces determine every invariant normal cubic residual. -/
theorem normalCubicResidual_eq_marked [Finite G] (X A B Y : Subgroup G)
    [IsElementaryAbelian 3 (X ⧸ pCore 2 X)] (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (hA : A ∈ normalCubicResiduals X) (hB : B ∈ normalCubicResiduals X)
    (hY : Y ∈ normalCubicResiduals X)
    (hne : normalCubicResidualImage X A ≠ normalCubicResidualImage X B)
    (g : normalizer (X : Set G))
    (hfix : ∀ z ∈ normalCubicResidualImage X A, normalCubicQuotientAction X g z = z)
    (hinv : ∀ z ∈ normalCubicResidualImage X B, normalCubicQuotientAction X g z = z⁻¹)
    (hnY : (g : G) ∈ normalizer (Y : Set G)) : Y = A ∨ Y = B := by
  have hs : (Y.subgroupOf X).map (X.normalizerMonoidHom g).toMonoidHom =
      Y.subgroupOf X := by
    rw [← normalCubicResidual_subgroupOf_conjugate X Y hY.1]
    exact congrArg (fun Z : Subgroup G => Z.subgroupOf X)
      (mem_normalizer_iff_map_conj_eq.mp hnY)
  have he := NormalCubicLines.invariant_eq_marked hX
    (A.subgroupOf X) (B.subgroupOf X) (Y.subgroupOf X)
    ((mem_normalCubicResiduals_iff X A hA.1).mp hA)
    ((mem_normalCubicResiduals_iff X B hB.1).mp hB)
    ((mem_normalCubicResiduals_iff X Y hY.1).mp hY)
    hne (X.normalizerMonoidHom g) hfix hinv hs
  have recover {Z : Subgroup G} (hZ : Z ≤ X) (he : Y.subgroupOf X = Z.subgroupOf X) :
      Y = Z := by
    have hm := congrArg (map X.subtype) he
    simpa only [map_subgroupOf_eq_of_le hY.1, map_subgroupOf_eq_of_le hZ] using hm
  exact he.imp (recover hA.1) (recover hB.1)

/-- The residual-preimage inverse recovers the original ambient subgroup. -/
theorem normalCubicResidual_recover {X Y : Subgroup G}
    (hY : Y ∈ normalCubicResiduals X) :
    (NormalCubicLines.lift (normalCubicResidualImage X Y)).map X.subtype = Y := by
  have hi := (mem_normalCubicResiduals_iff X Y hY.1).mp hY
  rw [normalCubicResidualImage, NormalCubicLines.lift_image _ hi.1.isSubnormal hi.2.1,
    map_subgroupOf_eq_of_le hY.1]

/-- Evaluation of the ambient correspondence uses the specified quotient image. -/
@[simp] theorem normalCubicResidualsEquivLines_apply [Finite G] (X : Subgroup G)
    [IsElementaryAbelian 3 (X ⧸ pCore 2 X)] (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (Y : normalCubicResiduals X) :
    (normalCubicResidualsEquivLines X hX Y).val = normalCubicResidualImage X Y.val := rfl

/-- Its inverse is the residual of the literal line preimage, embedded into G. -/
@[simp] theorem normalCubicResidualsEquivLines_symm_apply [Finite G] (X : Subgroup G)
    [IsElementaryAbelian 3 (X ⧸ pCore 2 X)] (hX : Nat.card (X ⧸ pCore 2 X) = 9)
    (A : {A : Subgroup (X ⧸ pCore 2 X) // Nat.card A = 3}) :
    ((normalCubicResidualsEquivLines X hX).symm A).val =
      (NormalCubicLines.lift A.val).map X.subtype := rfl

end Subgroup
