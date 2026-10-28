module

public import Theory.SpecificGroups.OrthogonalFourBinary.MarkedNine
public import Theory.SpecificGroups.OrthogonalFourBinary.CyclicFourOffenders
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Residual movement at a marked vector in the order-36 actor

The order-six point stabilizer contains a cubic rotation. A nonzero vector
fixed by this rotation lies in one definite plane, and the rotation moves the
other plane. For an order-four isometry whose square fixes the marked vector,
every fixed vector is a sum of a multiple of that vector and a cubic
displacement. The cubic belongs to the literal two-residual of the point
stabilizer, giving the fixed-space containment used in the marked component
construction.

The coordinate calculation uses the existing 72 isometries and 16 vectors;
no abstract replacement for the action or residual is made.
Source: Aschbacher--Smith 15.1.19(1), following the elementary-nine row of
15.1.16b and the natural O₄⁺(2) coordinates, printed pp.1092--1093.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace OrthogonalFourBinary.MarkedNine
open TerminalLines SylowGeometry
set_option synthInstance.maxSize 10000

private def b0 : Space := ((1,0),(0,0))
private def b1 : Space := ((0,1),(0,0))
private def b2 : Space := ((0,0),(1,0))
private def b3 : Space := ((0,0),(0,1))
private def samples (f : Space → Space) := (f b0,f b1,f b2,f b3)

private theorem samples_injective (e f : Space ≃ₗ[F] Space)
    (h : samples e = samples f) : e = f := by
  have h0 := congrArg (fun x => x.1) h
  have h1 := congrArg (fun x => x.2.1) h
  have h2 := congrArg (fun x => x.2.2.1) h
  have h3 := congrArg (fun x => x.2.2.2) h
  apply LinearEquiv.ext
  intro w
  have hw : w = w.1.1 • b0 + w.1.2 • b1 + w.2.1 • b2 + w.2.2 • b3 := by
    exact (show ∀ w : Space,
      w = w.1.1 • b0 + w.1.2 • b1 + w.2.1 • b2 + w.2.2 • b3 by decide +kernel) w
  rw [hw]
  change e _ = f _
  simp only [map_add,map_smul]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg (w.1.1 • ·) h0) (congrArg (w.1.2 • ·) h1))
    (congrArg (w.2.1 • ·) h2)) (congrArg (w.2.2 • ·) h3)

private def FourCode (k : Code) : Prop :=
  samples (fun v => eval k (eval k (eval k (eval k v)))) = samples id ∧
    samples (fun v => eval k (eval k v)) ≠ samples id

private instance (k : Code) : Decidable (FourCode k) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem fourCode_of_order (k : Code) (h : orderOf (codeMap k) = 4) : FourCode k := by
  constructor
  · have hh : codeMap k ^ 4 = 1 := h ▸ pow_orderOf_eq_one (codeMap k)
    have hv := congrArg (fun a : IsometryGroup => samples a.val) hh
    change samples (fun v => candidate k (candidate k (candidate k (candidate k v)))) = samples id at hv
    simpa only [candidate_eval] using hv
  · intro he
    have hh : codeMap k ^ 2 = 1 := by
      apply Subtype.ext
      apply samples_injective
      change samples (fun v => candidate k (candidate k v)) = samples id
      simpa only [candidate_eval] using he
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [h] at hd
    norm_num at hd

private theorem rotation_eval : ∀ i : RotationCode, ∀ v : Space,
    rotation i v = rotEval i v := by decide +kernel

set_option maxRecDepth 10000 in
private theorem finite_decomposition : ∀ k : Code, FourCode k →
    ∀ i : RotationCode, i ≠ 1 → ∀ z : Space, z ≠ 0 → rotEval i z = z →
    eval k (eval k z) = z → ∀ v : Space, eval k v = v →
    ∃ c : F, ∃ w : Space, v = c • z + (rotEval i w - w) := by
  decide +kernel

private theorem fixed_vector_decomposition (r a : IsometryGroup)
    (hr : orderOf r = 4) (ha : orderOf a = 3)
    (z : Space) (hz : z ≠ 0) (haz : a.val z = z) (hrz : (r ^ 2).val z = z)
    (v : Space) (hv : r.val v = v) :
    ∃ c : F, ∃ w : Space, v = c • z + (a.val w - w) := by
  have harot : a ∈ rotations := by
    rw [← residual_eq_rotations]
    apply mem_pResidual_of_orderOf_coprime
    rw [ha]
    decide
  obtain ⟨i,rfl⟩ := harot
  have hi : i ≠ 1 := by
    intro he
    simp [he] at ha
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective r
  have hfix : eval k (eval k z) = z := by
    change candidate k (candidate k z) = z at hrz
    simpa only [candidate_eval] using hrz
  have haz' : rotEval i z = z := by
    change rotation i z = z at haz
    simpa only [rotation_eval] using haz
  have hv' : eval k v = v := by
    change candidate k v = v at hv
    simpa only [candidate_eval] using hv
  obtain ⟨c,w,hw⟩ := finite_decomposition k (fourCode_of_order k hr) i hi z hz haz' hfix v hv'
  refine ⟨c,w,?_⟩
  change v = c • z + (rotation i w - w)
  simpa only [rotation_eval] using hw

/-- The literal two-residual of an order-six marked point stabilizer supplies
all displacement needed to contain the cyclic-four fixed space. -/
theorem fixedSpace_le_span_sup_residualCommutator {D : Type*} [Group D] [Finite D]
    (f : D →* IsometryGroup) (hf : Function.Injective f)
    (S : Subgroup D) [IsCyclic S] (hS : Nat.card S = 4)
    (z : Space) (hz : z ≠ 0)
    (hfix : ∀ a ∈ S, a ^ 2 = 1 → (f a).val z = z)
    (hK : Nat.card (pointStabilizer f z) = 6) :
    fixedSpace (naturalRepresentation.comp f) S ≤
      Submodule.span F {z} ⊔ subspaceCommutator (naturalRepresentation.comp f) ⊤
        ((pResidual 2 (pointStabilizer f z)).map (pointStabilizer f z).subtype) := by
  classical
  let K := pointStabilizer f z
  obtain ⟨r,hrgen⟩ := IsCyclic.exists_generator (α := S)
  have hr : orderOf (r : D) = 4 := (Subgroup.orderOf_coe r).trans
    ((orderOf_eq_card_of_forall_mem_zpowers hrgen).trans hS)
  have hr4 : (r : D) ^ 4 = 1 := hr ▸ pow_orderOf_eq_one (r : D)
  have hrfix : (f (r : D) ^ 2).val z = z := by
    rw [← map_pow]
    apply hfix _ (S.pow_mem r.property 2)
    simpa only [← pow_mul] using hr4
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hK]; decide)
  have hfa : orderOf (f (a : D)) = 3 :=
    (orderOf_injective f hf (a : D)).trans ((Subgroup.orderOf_coe a).trans ha)
  have haz : (f (a : D)).val z = z := a.property
  have hares : a ∈ pResidual 2 K := by
    apply mem_pResidual_of_orderOf_coprime
    rw [ha]
    decide
  intro v hv
  have hrv : (f (r : D)).val v = v := hv r
  obtain ⟨c,w,hw⟩ := fixed_vector_decomposition (f r) (f a)
    ((orderOf_injective f hf r).trans hr) hfa z hz haz hrfix v hrv
  rw [hw]
  apply Submodule.add_mem_sup
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton z))
  · exact Submodule.subset_span ⟨(a : D),mem_map_of_mem K.subtype hares,w,
      Submodule.mem_top,rfl⟩

/-- The marked witness for the elementary-nine actor also retains its literal
residual displacement and the placement of every Sylow-fixed vector. -/
theorem exists_marked_vector_with_movement {D : Type*} [Group D] [Finite D]
    (f : D →* IsometryGroup) (hf : Function.Injective f) (hc : Nat.card D = 36)
    (S : Subgroup D) [IsCyclic S] (hS : Nat.card S = 4) :
    ∃ z : Space, z ≠ 0 ∧
      (∀ a ∈ S, a ^ 2 = 1 → (f a).val z = z) ∧
      pointStabilizer f z ⊔ S = ⊤ ∧
      Nat.card (pointStabilizer f z) = 6 ∧
      (∃ P : Sylow 2 (pointStabilizer f z),
        (P : Subgroup (pointStabilizer f z)).map (pointStabilizer f z).subtype =
          S ⊓ pointStabilizer f z) ∧
      fixedSpace (naturalRepresentation.comp f) S ≤
        Submodule.span F {z} ⊔ subspaceCommutator (naturalRepresentation.comp f) ⊤
          ((pResidual 2 (pointStabilizer f z)).map (pointStabilizer f z).subtype) := by
  obtain ⟨z,hz,hfix,hgen,hK,hSyl⟩ := exists_marked_vector f hf hc S hS
  exact ⟨z,hz,hfix,hgen,hK,hSyl,
    fixedSpace_le_span_sup_residualCommutator f hf S hS z hz hfix hK⟩

end OrthogonalFourBinary.MarkedNine
