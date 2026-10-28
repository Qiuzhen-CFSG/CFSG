module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanWeights
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# The positive table forces the two source Cartan cross actions

The geometric hexagon count gives |U| = q⁶. Positive collection is therefore
bijective in the consumer's A--F order. Conjugating the FE equation by any
Cartan element and comparing these unique coordinates yields its A and C
coefficient identities, without assuming that the Cartan acts by scalars.

The short coroot centralizes A and acts on F by a². The A identity forces
its action on E to be a⁻³. The long coroot centralizes C and acts on E by
a²; the C identity forces its action on F to be a⁻¹. Injectivity of squaring
in characteristic two finishes both calculations, including q=2 and q=4.
The fixed-root assertions use the existing orthogonal centralization deduced
from the positive table. No representation classification is invoked here.

These actions discharge both independent cross-action premises in
WeightApplication. All Cartan, Weyl and braid clauses now follow from the
remaining PartialPositiveData on the actual reflection-aligned pinnings.
Constructing that lower positive data from 6E(a) is still required; this
module does not claim the source recognition theorem.

Source: Fong--Seitz II (9.13)--(9.21), printed pp.215--217. This is a
coordinate-covariance alternative to the final Cartan calculation; all
products and conjugations follow the published left-conjugation consumer.
The literal original/geometric application is ForcedCartanApplication.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

/-- Positive collection on the same source U has unique A--F parameters. -/
theorem alignedSourceRoots_product_injective (hm : rotationOrder Q = 6)
    (hrel : (alignedSourceRoots Q split hK μ n short).CharTwoRelations) :
    Function.Injective (alignedSourceRoots Q split hK μ n short).product := by
  let L := alignedSourceRoots Q split hK μ n short
  have hgen : L.generated = split.U := alignedSourceRoots_generated Q split hK μ n short hm
  let f : (Fin 6 → F) → split.U := fun a => ⟨L.product a, hgen ▸ L.product_mem_generated a⟩
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨a,ha⟩ := (L.mem_generated_iff hrel.collection u).mp (hgen.symm ▸ u.property)
    exact ⟨a,Subtype.ext ha⟩
  have hc : Nat.card (Fin 6 → F) = Nat.card split.U := by
    rw [Nat.card_fun, Nat.card_fin, unipotent_card_even Q split 3 hm,
      simpleRoot_card Q split 0 (hK 0) (μ 0), simpleRoot_card Q split 1 (hK 1) (μ 1)]
    simp only [← pow_two, ← pow_mul]
  have hi := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc⟩).1
  intro a b hab
  exact hi (Subtype.ext hab)

private theorem exists_cartan_root_parameter {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (i : Fin 6) (a : F) :
    ∃ b : F, t * (alignedSourceRoots Q split hK μ n short).x i a * t⁻¹ =
      (alignedSourceRoots Q split hK μ n short).x i b := by
  have hx : (alignedSourceRoots Q split hK μ n short).x i a ∈ positiveCarrier Q split short i := by
    rw [← alignedSourceRoots_range Q split hK μ n short i]
    exact ⟨.ofAdd a,rfl⟩
  have hh := (mem_normalizer_iff.mp (positiveCarrier_torus_normalizes Q split short i ht) _).mp hx
  rw [← alignedSourceRoots_range Q split hK μ n short i] at hh
  obtain ⟨b,hb⟩ := hh
  exact ⟨b.toAdd,hb.symm⟩

omit [Finite F] [CharP F 2] in
private theorem fe_coordinate_covariance {Y : Type*} [Group Y]
    (L : PositiveRoots F Y) (R : L.CharTwoRelations) (hi : Function.Injective L.product)
    (σ : MulAut Y) (f : Fin 6 → F → F)
    (hf : ∀ i a, σ (L.x i a) = L.x i (f i a)) (z e : F) :
    f 0 (e^2*z^3) = (f 4 e)^2*(f 5 z)^3 ∧
    f 2 (e*z^2) = f 4 e*(f 5 z)^2 := by
  have he := congrArg σ (R.fe z e)
  simp only [map_mul,hf] at he
  rw [R.fe] at he
  have hp : L.product ![(f 4 e)^2*(f 5 z)^3, f 4 e*(f 5 z)^3,
      f 4 e*(f 5 z)^2, f 4 e*f 5 z, f 4 e,f 5 z] =
    L.product ![f 0 (e^2*z^3),f 1 (e*z^3),f 2 (e*z^2),f 3 (e*z),f 4 e,f 5 z] := he
  have hh := hi hp
  exact ⟨(congrFun hh 0).symm,(congrFun hh 2).symm⟩

/-- The actual short coroot acts on the long simple root by the inverse cube.
The scalar is forced by the highest FE coordinate, even over F₂ and F₄. -/
theorem alignedTorus_short_cross_action (hm : rotationOrder Q = 6)
    (R : (alignedSourceRoots Q split hK μ n short).CharTwoRelations) (a : Fˣ) (b : F) :
    alignedTorusHom Q split short (hK short) (μ short) (n short) a *
      (alignedSourceRoots Q split hK μ n short).x 4 b *
      (alignedTorusHom Q split short (hK short) (μ short) (n short) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 4 ((a : F)⁻¹^3*b) := by
  let L := alignedSourceRoots Q split hK μ n short
  let t := alignedTorusHom Q split short (hK short) (μ short) (n short) a
  have ht : t ∈ Q.tits.B ⊓ Q.tits.N := alignedTorus_mem_cartan Q split _ _ _ _ a
  choose f hf using (exists_cartan_root_parameter Q split hK μ n short ht)
  have hinj (i : Fin 6) : Function.Injective (L.x i) :=
    (alignedSourceRoots_injective Q split hK μ n short i).comp Multiplicative.ofAdd.injective
  have hzero (c : F) : f 0 c = c := by
    apply hinj 0
    rw [← hf]
    have hc := aligned_short_centralizes Q split hK μ n short hm R.toCommutingRelations
      (show t ∈ rankOne Q split short from
        (show t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split short from
          (alignedTorusHom_range Q split short (hK short) (μ short) (n short)) ▸ ⟨a,rfl⟩).2)
    have hx : L.x 0 c ∈ positiveCarrier Q split short 0 := by
      rw [← alignedSourceRoots_range Q split hK μ n short 0]
      exact ⟨.ofAdd c,rfl⟩
    rw [← mem_centralizer_iff.mp hc _ hx,mul_assoc,mul_inv_cancel,mul_one]
  have hfive : f 5 1 = (a : F)^2 := by
    apply hinj 5
    rw [← hf]
    simpa only [L,t,alignedSourceRoots,PositiveRoots.x,Matrix.cons_val,alignedTorusHom_apply,mul_one] using alignedTorus_root Q split short (hK short) (μ short) (n short) a 1
  have he := (fe_coordinate_covariance L R
    (alignedSourceRoots_product_injective Q split hK μ n short hm R)
    (MulAut.conj t) f hf 1 b).1
  rw [hzero,hfive,one_pow,mul_one] at he
  have hs : b = f 4 b * (a : F)^3 := CharTwo.sq_injective (he.trans (by ring))
  have hb : f 4 b = (a : F)⁻¹^3*b := by
    calc
      f 4 b = (a : F)⁻¹^3*(f 4 b * (a : F)^3) := by field_simp
      _ = _ := congrArg (fun c : F => (a : F)⁻¹^3*c) hs.symm
  exact (hf 4 b).trans (congrArg (L.x 4) hb)

/-- The actual long coroot acts on the short simple root by the inverse.
The scalar is forced by the middle FE coordinate, even over F₂ and F₄. -/
theorem alignedTorus_long_cross_action (hm : rotationOrder Q = 6)
    (R : (alignedSourceRoots Q split hK μ n short).CharTwoRelations) (a : Fˣ) (b : F) :
    alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a *
      (alignedSourceRoots Q split hK μ n short).x 5 b *
      (alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a)⁻¹ =
        (alignedSourceRoots Q split hK μ n short).x 5 ((a : F)⁻¹*b) := by
  let L := alignedSourceRoots Q split hK μ n short
  let t := alignedTorusHom Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short)) a
  have ht : t ∈ Q.tits.B ⊓ Q.tits.N := alignedTorus_mem_cartan Q split _ _ _ _ a
  choose f hf using (exists_cartan_root_parameter Q split hK μ n short ht)
  have hinj (i : Fin 6) : Function.Injective (L.x i) :=
    (alignedSourceRoots_injective Q split hK μ n short i).comp Multiplicative.ofAdd.injective
  have htwo (c : F) : f 2 c = c := by
    apply hinj 2
    rw [← hf]
    have hc := aligned_long_centralizes Q split hK μ n short hm R.toCommutingRelations
      (show t ∈ rankOne Q split (1-short) from
        (show t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split (1-short) from
          (alignedTorusHom_range Q split (1-short) (hK (1-short)) (μ (1-short)) (n (1-short))) ▸ ⟨a,rfl⟩).2)
    have hx : L.x 2 c ∈ positiveCarrier Q split short 2 := by
      rw [← alignedSourceRoots_range Q split hK μ n short 2]
      exact ⟨.ofAdd c,rfl⟩
    rw [← mem_centralizer_iff.mp hc _ hx,mul_assoc,mul_inv_cancel,mul_one]
  have hfour : f 4 1 = (a : F)^2 := by
    apply hinj 4
    rw [← hf]
    simpa only [L,t,alignedSourceRoots,PositiveRoots.x,Matrix.cons_val,alignedTorusHom_apply,mul_one] using alignedTorus_root Q split (1-short)
      (hK (1-short)) (μ (1-short)) (n (1-short)) a 1
  have he := (fe_coordinate_covariance L R
    (alignedSourceRoots_product_injective Q split hK μ n short hm R)
    (MulAut.conj t) f hf b 1).2
  rw [htwo,hfour,one_mul] at he
  have hs : b = (a : F)*f 5 b := CharTwo.sq_injective (he.trans (by ring))
  have hb : f 5 b = (a : F)⁻¹*b := by
    calc
      f 5 b = (a : F)⁻¹*((a : F)*f 5 b) := by field_simp
      _ = _ := congrArg (fun c : F => (a : F)⁻¹*c) hs.symm
  exact (hf 5 b).trans (congrArg (L.x 5) hb)

/-- The positive equations determine every remaining Borel--Weyl clause
on the constructed source maps. No separate Cartan-action premise remains. -/
theorem sourceBorelWeyl_relations_of_positive (hm : rotationOrder Q = 6)
    (R : (alignedSourceRoots Q split hK μ n short).CharTwoRelations) :
    (sourceBorelWeyl Q split hK μ n short split.abelian).Relations := by
  obtain ⟨hE,hF⟩ := sourceBorelWeyl_simple_weights_of_cross_actions
    Q split hK μ n short split.abelian
    (alignedTorus_short_cross_action Q split hK μ n short hm R)
    (alignedTorus_long_cross_action Q split hK μ n short hm R)
  exact {
    toCharTwoRelations := R
    torus_root := sourceBorelWeyl_torus_root_of_simple_weights
      Q split hK μ n short split.abelian hE hF
    r_sq := sourceBorelWeyl_r_sq Q split hK μ n short split.abelian
    s_sq := sourceBorelWeyl_s_sq Q split hK μ n short split.abelian
    braid := sourceBorelWeyl_braid Q split hK μ n short split.abelian hm R.toCommutingRelations
    r_torus := sourceBorelWeyl_r_torus_of_simple_weight Q split hK μ n short split.abelian
      (fun l m => by simpa only [mul_one] using hE l m 1)
    s_torus := sourceBorelWeyl_s_torus_of_simple_weight Q split hK μ n short split.abelian
      (fun l m => by simpa only [mul_one] using hF l m 1)
    rA := sourceBorelWeyl_rA Q split hK μ n short split.abelian
    rB := sourceBorelWeyl_rB Q split hK μ n short split.abelian
    rC := sourceBorelWeyl_rC Q split hK μ n short split.abelian hm R.toCommutingRelations
    rD := sourceBorelWeyl_rD Q split hK μ n short split.abelian
    rF := sourceBorelWeyl_rF Q split hK μ n short split.abelian
    sA := sourceBorelWeyl_sA Q split hK μ n short split.abelian hm R.toCommutingRelations
    sB := sourceBorelWeyl_sB Q split hK μ n short split.abelian
    sC := sourceBorelWeyl_sC Q split hK μ n short split.abelian
    sD := sourceBorelWeyl_sD Q split hK μ n short split.abelian
    sE := sourceBorelWeyl_sE Q split hK μ n short split.abelian
    long_word := sourceBorelWeyl_long_word Q split hK μ n short split.abelian
    short_word := sourceBorelWeyl_short_word Q split hK μ n short split.abelian }

/-- The existing lower positive input now supplies the entire presentation
without additional common-field cross actions, in either orientation. -/
theorem sourceBorelWeyl_relations_of_partial (hm : rotationOrder Q = 6)
    (d₀ : PartialPositiveData (alignedSourceRoots Q split hK μ n short)) :
    (sourceBorelWeyl Q split hK μ n short split.abelian).Relations :=
  sourceBorelWeyl_relations_of_positive Q split hK μ n short hm
    (aligned_positive_relations_of_partial Q split hK μ n short hm d₀)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
