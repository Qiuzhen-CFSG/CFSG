module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCubicGeneration
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallSquareDegree
public import Theory.GroupTheory.FourCubicKernel
public import Theory.Representation.BinaryOffender.ConjugateSubgroupSaturation
public import Theory.Representation.BinaryOffender.ReducedCentralQuotient

/-!
# A cubic-pair budget for the original product actor

The actual elementary cubic plane is a product of its cyclic projections.
One conjugate therefore generates the full PSL square together with it.
For a faithful binary action with trivial two-core, passage to the quotient
by the full fixed space preserves faithfulness. The native prime-square
degree bound then forces the original cubic fixed codimension above eight.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree

private theorem prod_join {X Y : Type*} [Group X] [Group Y]
    (A C : Subgroup X) (B D : Subgroup Y) :
    A.prod B ⊔ C.prod D = (A ⊔ C).prod (B ⊔ D) := by
  apply le_antisymm (sup_le (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right))
  let H := A.prod B ⊔ C.prod D
  have hx : A ⊔ C ≤ H.comap (MonoidHom.inl X Y) := by
    exact sup_le (fun a ha => mem_sup_left ⟨ha,one_mem _⟩)
      (fun c hc => mem_sup_right ⟨hc,one_mem _⟩)
  have hy : B ⊔ D ≤ H.comap (MonoidHom.inr X Y) := by
    exact sup_le (fun b hb => mem_sup_left ⟨one_mem _,hb⟩)
      (fun d hd => mem_sup_right ⟨one_mem _,hd⟩)
  intro z hz
  have hh := H.mul_mem (hx hz.1) (hy hz.2)
  change (z.1,1) * (1,z.2) ∈ H at hh
  simpa only [Prod.mk_mul_mk,mul_one,one_mul] using hh

private theorem prod_map_conj {X Y : Type*} [Group X] [Group Y]
    (A : Subgroup X) (B : Subgroup Y) (x : X) (y : Y) :
    (A.prod B).map (MulAut.conj (x,y)).toMonoidHom =
      (A.map (MulAut.conj x).toMonoidHom).prod (B.map (MulAut.conj y).toMonoidHom) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨mem_map_of_mem _ hw.1,mem_map_of_mem _ hw.2⟩
  · rintro ⟨⟨a,ha,he⟩,⟨b,hb,hf⟩⟩
    exact ⟨(a,b),⟨ha,hb⟩,Prod.ext he hf⟩

/-- The literal cubic plane and one conjugate generate the prime-field PSL square. -/
theorem cubic_plane_sup_conjugate_eq_top (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (P : Subgroup (PSL(2,ZMod p) × PSL(2,ZMod p)))
    [IsElementaryAbelian 3 P]
    [IsCyclic (P.map (MonoidHom.fst _ _))]
    [IsCyclic (P.map (MonoidHom.snd _ _))] (hP : Nat.card P = 9) :
    ∃ g, P ⊔ P.map (MulAut.conj g).toMonoidHom = ⊤ := by
  let A := P.map (MonoidHom.fst _ _)
  let B := P.map (MonoidHom.snd _ _)
  obtain ⟨hA,hB⟩ := Theory.GroupTheory.cubic_plane_projection_cards P hP
  have he : P = A.prod B := eq_of_le_of_card_ge
    (fun z hz => ⟨mem_map_of_mem _ hz,mem_map_of_mem _ hz⟩) (by
      rw [Nat.card_congr (prodEquiv A B).toEquiv,Nat.card_prod,hP]
      change 9 ≥ Nat.card A * Nat.card B
      rw [hA,hB])
  obtain ⟨x,hx⟩ := cubic_sup_conjugate_eq_top p hp A hA
  obtain ⟨y,hy⟩ := cubic_sup_conjugate_eq_top p hp B hB
  refine ⟨(x,y),?_⟩
  rw [he,prod_map_conj,prod_join,hx,hy,top_prod_top]

/-- Two conjugate subgroup generators and the actual prime-square divisor
force fixed codimension greater than eight. -/
theorem prime_square_fixedCodim_gt_eight_of_conjugate_pair
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hc : pCore 2 G = ⊥) {p : ℕ} (hp : p.Prime)
    (hm : p % 24 = 11 ∨ p % 24 = 13) (hdiv : p^2 ∣ Nat.card G)
    (P : Subgroup G) (g : G) (hgen : P ⊔ P.map (MulAut.conj g).toMonoidHom = ⊤) :
    8 < Representation.BinaryOffender.fixedCodim ρ P := by
  open Representation.BinaryOffender in
  have hfaith : Function.Injective (fixedQuotient ρ ⊤) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    let x : (⊤ : Subgroup G) := ⟨a,mem_top a⟩
    have hx : x ∈ (fixedQuotientRepresentation ρ ⊤).ker :=
      (mem_fixedQuotient_ker_iff ρ ⊤ x).mpr ((quotient_kernel_iff ρ ⊤ a).mp ha)
    have hh := fixedQuotient_ker_le_pCore ρ hf ⊤ hx
    rw [pCore_eq_comap_of_normal,hc] at hh
    exact hh
  open Representation.BinaryOffender in
  have hdegree := prime_square_degree_gt_sixteen (fixedQuotient ρ ⊤) hfaith hp hm hdiv
  have h1 : P.map (MulAut.conj (1:G)).toMonoidHom = P := by
    rw [map_one]
    change P.map (MonoidHom.id G) = P
    exact map_id P
  open Representation.BinaryOffender in
  have hbound := fixedCodim_le_card_mul_of_subgroup_conjugates ρ ⊤ P
    (fun b : Bool => if b then g else 1) (by
      simpa only [iSup_bool_eq,Bool.false_eq_true,if_false,if_true,h1,sup_comm] using hgen.ge)
  change 16 < Representation.BinaryOffender.fixedCodim ρ ⊤ at hdegree
  simp only [Fintype.card_bool] at hbound
  omega

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree
