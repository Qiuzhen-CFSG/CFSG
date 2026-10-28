module
public import Theory.SpecificGroups.PSL3Four.NormalElementaryComponent
public import Theory.SpecificGroups.PSL3Four.ElementaryCubicSplitting
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.BinaryOffender.Defs

/-!
# Ranks of the two opposite-image factors

An elementary subgroup of a Sylow two-subgroup which is invariant under a
nontrivial diagram actor meets a normal PSL₃(4) component in at most four
elements. Transport the original Sylow intersection to UT₃; the actor
exchanges the two root planes, so their invariant elementary subgroup lies
in the highest root of order four.

For an elementary subgroup inside K C(K), an order-three Cartan in K
splits it into its intersections with K and C(K). The residual factor
cannot have order two: its normalizer would centralize it, contrary to the
fixed-point-free Cartan action there. Thus its rank is zero or two, and
the two factor ranks add to the full rank.

The literal opposite-action application is in Chapter 12's
EscapeModulesFactorRanks. This supplies the residual rank bound needed
for the remaining displacement obstruction; it does not exclude the
centralizer factor or assert abelianness of the source span.

Source: Aschbacher--Smith E.2.7 and 5.1.23, printed pp.219,645--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3Even.MinimalParabolicWitness
namespace Matrix.PSL3Four.NormalElementaryFactors
variable {F₀ : Type*} [Field F₀] [Finite F₀] [CharP F₀ 2]

private theorem card_bound (hF : Nat.card F₀ = 4)
    (P : Sylow 2 PSL(3,F₀)) (E : Subgroup PSL(3,F₀))
    [IsElementaryAbelian 2 E] (hEP : E ≤ (P : Subgroup PSL(3,F₀)))
    (a : MulAut PSL(3,F₀))
    (hP : (P : Subgroup PSL(3,F₀)).map a.toMonoidHom = P)
    (hE : E.map a.toMonoidHom = E) (hd : a ∉ diagramTrivial F₀) :
    Nat.card E ≤ 4 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F₀) P
    (unipotentSylow F₀ (n := 2) (by decide) (by simpa using hF))
  let γ : MulAut PSL(3,F₀) := MulAut.conj g
  let A := E.map γ.toMonoidHom
  let α := γ * a * γ⁻¹
  have hPU : (P : Subgroup PSL(3,F₀)).map γ.toMonoidHom = unipotent F₀ :=
    congrArg Sylow.toSubgroup hg
  have hinv (Q : Subgroup PSL(3,F₀)) (hQ : Q.map a.toMonoidHom = Q) :
      (Q.map γ.toMonoidHom).map α.toMonoidHom = Q.map γ.toMonoidHom := by
    have hh : α.toMonoidHom.comp γ.toMonoidHom = γ.toMonoidHom.comp a.toMonoidHom := by
      ext x
      change γ (a (γ⁻¹ (γ x))) = γ (a x)
      rw [MulAut.inv_apply_self]
    rw [Subgroup.map_map,hh,← Subgroup.map_map,hQ]
  have hU : (unipotent F₀).map α.toMonoidHom = unipotent F₀ := by
    rw [← hPU]
    exact hinv _ hP
  have hd' : diagramAction F₀ (n := 2) (by decide) (by simpa using hF) α ≠ 1 := by
    intro he
    apply hd
    rw [← diagramAction_ker F₀ (n := 2) (by decide) (by simpa using hF)]
    let δ := diagramAction F₀ (n := 2) (by decide) (by simpa using hF)
    change δ (γ * a * γ⁻¹) = 1 at he
    change δ a = 1
    rw [map_mul,map_mul,map_inv] at he
    exact mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (δ γ)).symm)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map γ.toMonoidHom
  have hAZ := elementary_invariant_le_center F₀ (n := 2) (by decide)
    (by simpa using hF) α hU hd' A (by rw [← hPU]; exact map_mono hEP) (hinv _ hE)
  have hc : Nat.card (projectiveCenter F₀) = 4 := by
    rw [projectiveCenter,card_map_of_injective (projective_injective F₀),card_Z,hF]
  have hh := Nat.card_le_card_of_injective (inclusion hAZ) (inclusion_injective hAZ)
  rw [hc,card_map_of_injective γ.injective] at hh
  exact hh

variable {X : Type*} [Group X] [Finite X]

/-- The diagram actor bounds the residual intersection of a normal elementary
Sylow subgroup, using the original embedding and conjugation action. -/
theorem residual_intersection_card_le_four
    (K : Subgroup X) [K.Normal] (P : Sylow 2 X)
    (E : Subgroup X) [IsElementaryAbelian 2 E]
    (hEP : E ≤ (P : Subgroup X)) (hPE : (P : Subgroup X) ≤ normalizer (E : Set X))
    (hF : Nat.card F₀ = 4) (e : K ≃* PSL(3,F₀))
    (t : X) (ht : t ∈ (P : Subgroup X))
    (a : MulAut K) (b : MulAut PSL(3,F₀))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F₀) :
    Nat.card (E ⊓ K : Subgroup X) ≤ 4 := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal K
  let A := E.subgroupOf K
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let A' := A.map e.toMonoidHom
  let f : A →* E := K.subtype.restrict (fun _ hx => hx)
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun y : E => (y : X)) he))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective f hf
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map e.toMonoidHom
  have hAQ : A ≤ (Q : Subgroup K) := by rw [hQ]; exact comap_mono hEP
  have hQA : (Q : Subgroup K).map a.toMonoidHom = Q := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hQ] at hx ⊢
      change (a x : X) ∈ P
      rw [ha]
      exact (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem ht hx)
        ((P : Subgroup X).inv_mem ht)
    · rw [card_map_of_injective a.injective]
  have hAA : A.map a.toMonoidHom = A := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change (a x : X) ∈ E
      rw [ha]
      exact (mem_normalizer_iff.mp (hPE ht) x).mp hx
    · rw [card_map_of_injective a.injective]
  have hcomp : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom :=
    MonoidHom.ext (fun k => (hb k).symm)
  have hR : (R : Subgroup PSL(3,F₀)).map b.toMonoidHom = R := by
    change ((Q : Subgroup K).map e.toMonoidHom).map b.toMonoidHom = _
    rw [Subgroup.map_map,hcomp,← Subgroup.map_map,hQA]
    rfl
  have hA' : A'.map b.toMonoidHom = A' := by
    change (A.map e.toMonoidHom).map b.toMonoidHom = _
    rw [Subgroup.map_map,hcomp,← Subgroup.map_map,hAA]
  have hc := card_bound hF R A' (map_mono hAQ) b hR hA' hd
  have he : Nat.card A = Nat.card (E ⊓ K : Subgroup X) := by
    let j : A ≃ (E ⊓ K : Subgroup X) := {
      toFun := fun x => ⟨x, x.property, x.val.property⟩
      invFun := fun x => ⟨⟨x,x.property.2⟩,x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact Nat.card_congr j
  rw [card_map_of_injective e.injective,he] at hc
  exact hc

local notation "rank₂" => Representation.BinaryOffender.rank
open scoped IsMulCommutative

/-- The Cartan splitting has residual rank zero or two; the ranks of the two
literal intersections add to the full elementary rank. -/
theorem split_ranks (K E B : Subgroup X) [K.Normal] [IsElementaryAbelian 2 E]
    (e : K ≃* PSL) (hBE : B ≤ normalizer (E : Set X)) (hBK : B ≤ K)
    (hB : Nat.card B = 3) (hE : E ≤ K ⊔ centralizer (K : Set X))
    (hsmall : Nat.card (E ⊓ K : Subgroup X) ≤ 4) :
    (rank₂ (E ⊓ K) = 0 ∨ rank₂ (E ⊓ K) = 2) ∧
      rank₂ E = rank₂ (E ⊓ K) + rank₂ (E ⊓ centralizer (K : Set X)) := by
  let R := E ⊓ K
  let Z := E ⊓ centralizer (K : Set X)
  obtain ⟨hs,hfix,_,hdis⟩ := ElementaryCubicSplitting.elementary_split K E B e hBE hBK hB hE
  have hcard (A : Subgroup X) (hA : A ≤ E) : Nat.card A = 2 ^ rank₂ A := by
    let : IsElementaryAbelian 2 A :=
      IsElementaryAbelian.of_injective (inclusion hA) (inclusion_injective hA)
    obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [Representation.BinaryOffender.rank,hm,Nat.log_pow (by decide : 1 < 2)]
  have hrle : rank₂ R ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hcard R inf_le_left]
    exact hsmall
  have hrne : rank₂ R ≠ 1 := by
    intro hr
    have hRcard : Nat.card R = 2 := by rw [hcard R inf_le_left,hr,pow_one]
    have hBR : B ≤ normalizer (R : Set X) :=
      (le_inf hBE (hBK.trans K.le_normalizer)).trans inf_normalizer_le_normalizer_inf
    have hRB : R ≤ centralizer (B : Set X) := le_centralizer_iff.mp
      (hBR.trans (normalizer_le_centralizer_of_card_two R hRcard))
    have hRZ : R ≤ Z := by
      change R ≤ E ⊓ centralizer (K : Set X)
      rw [← hfix]
      exact le_inf inf_le_left hRB
    have hz : R = ⊥ := bot_unique ((le_inf le_rfl hRZ).trans hdis.le_bot)
    have hc := card_eq_one.mpr hz
    omega
  have hnorm : Z ≤ normalizer (R : Set X) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz r hr
    exact setLike_mul_comm (s := E) hr.1 hz.1
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes R Z hnorm
  rw [hcard R inf_le_left,hcard Z inf_le_left,hdis.eq_bot,Subgroup.card_bot,
    one_mul,← hs,hcard E le_rfl,← pow_add] at hc
  have hchoice : rank₂ R = 0 ∨
      rank₂ R = 2 := by omega
  exact ⟨hchoice,(Nat.pow_right_injective (by decide : 2 ≤ 2) hc).symm⟩

end Matrix.PSL3Four.NormalElementaryFactors
