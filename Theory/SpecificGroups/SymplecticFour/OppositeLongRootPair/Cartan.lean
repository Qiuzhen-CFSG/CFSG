module
public import Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair.Recognition
public import Theory.SpecificGroups.SymplecticFour.RootCoreTori.Quotients
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Geometry

/-!
# Detecting the opposite pair from the point-local quotient

An actor preserving the two opposite coordinate lines and centralizing
pointLocal/O₂(pointLocal) has trivial middle SL₂ block. Removing its
scalar on the first line leaves an element of the point radical;
preservation of the opposite line kills all three radical coordinates.
Thus the actor is the scalar torus of the original opposite pair.
The final criterion transports this calculation to any symplectic frame.

This is the matrix input for the Cartan-compatible opposite choice in
Aschbacher--Smith 11.5.7, printed p.783.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Matrix
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair
open DiagramAutomorphisms
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- The scalar torus on the first hyperbolic plane belongs to the literal pair. -/
theorem diagonal_mem_pair (s : Fˣ) : diagonalTorus s 1 ∈ pair := by
  rw [← embedding_range]
  let A : SpecialLinearGroup (Fin 2) F :=
    ⟨Matrix.diagonal ![(s:F),(↑s⁻¹:F)], by simp⟩
  refine ⟨A,?_⟩
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [embedding,matrix,A,diagonalTorus,Matrix.diagonal]

/-- A point-parabolic actor trivial on the literal Levi quotient and
preserving the opposite point is a scalar on the first hyperbolic plane. -/
theorem scalar_of_quotient_eq_one (x : pointParabolic (F := F))
    (hq : pointParabolicQuotient x = 1)
    (ho : x.val ∈ stabilizer (F ∙ (Pi.single (.inr 0) 1 : Vector F))) :
    ∃ s : Fˣ, x.val = diagonalTorus s 1 := by
  let s := determinantCharacter (point F) x
  let t : pointParabolic (F := F) :=
    ⟨diagonalTorus s 1,(diagonalTorus_mem_borel s 1).1⟩
  have ht : determinantCharacter (point F) t = s := diagonalTorus_point_character s 1
  have hqt : pointParabolicQuotient t = 1 := by
    apply Subtype.ext
    rw [pointParabolicQuotient_torus]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have hl : (x * t⁻¹).val ∈ pointLocal := by
    refine ⟨x * t⁻¹, ?_, rfl⟩
    change determinantCharacter (point F)
      ((⟨x.val,x.property⟩ : stabilizer (point F)) * ⟨t.val,t.property⟩⁻¹) = 1
    rw [map_mul,map_inv,ht]
    exact mul_inv_cancel s
  let a : pointLocal (F := F) := ⟨(x * t⁻¹).val,hl⟩
  have ha : a ∈ pointRadical := by
    change pointParabolicQuotient (x * t⁻¹) = 1
    rw [map_mul,map_inv,hq,hqt]
    simp
  have hto : t.val ∈ stabilizer (F ∙ (Pi.single (.inr 0) 1 : Vector F)) := by
    apply (mem_stabilizer_iff _ _).mpr
    intro v hv
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hv
    change toLinear t.val (b • _) ∈ _
    rw [map_smul]
    apply Submodule.smul_mem
    have he : toLinear t.val (Pi.single (.inr 0) 1 : Vector F) =
        (↑s⁻¹ : F) • Pi.single (.inr 0) 1 := by
      ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [t,diagonalTorus,Matrix.mulVec_single,Matrix.diagonal]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hao : a.val ∈ stabilizer (F ∙ (Pi.single (.inr 0) 1 : Vector F)) :=
    (stabilizer _).mul_mem ho ((stabilizer _).inv_mem hto)
  have he := pointRadical_eq_element a ha
  have hv := (mem_stabilizer_iff _ _).mp hao (Pi.single (.inr 0) 1)
    (Submodule.mem_span_singleton_self _)
  obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hv
  rw [he] at hb
  have hu : a.val.val (.inl 1) (.inr 0) = 0 := by
    have h := congrFun hb (.inl 1)
    simpa [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single] using h.symm
  have hv : a.val.val (.inr 1) (.inr 0) = 0 := by
    have h := congrFun hb (.inr 1)
    simpa [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single] using h.symm
  have hz : a.val.val (.inl 0) (.inr 0) = 0 := by
    have h := congrFun hb (.inl 0)
    simpa [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single] using h.symm
  have ha1 : a = 1 := by rw [he,hu,hv,hz,pointRadicalElement_zero]
  refine ⟨s,?_⟩
  have hh : x.val * t.val⁻¹ = 1 := congrArg Subtype.val ha1
  exact mul_inv_eq_one.mp hh

variable [Finite F]
/-- Centralizing the actual point-local quotient kills the middle SL₂ block. -/
theorem quotient_eq_one_of_commutators {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)
    (x : pointParabolic (F := F))
    (hc : ∀ l ∈ pointLocal (F := F), ⁅x.val,l⁆ ∈ pointLocal.pCoreIn 2) :
    pointParabolicQuotient x = 1 := by
  have hz : pointParabolicQuotient x ∈ center (SpecialLinearGroup (Fin 2) F) := by
    apply mem_center_iff.mpr
    intro b
    obtain ⟨l,rfl⟩ := pointQuotient_surjective b
    have hc := hc l.val l.property
    change ⁅x.val,l.val⁆ ∈ (pCore 2 pointLocal).map pointLocal.subtype at hc
    rw [pointLocal_core_eq hF hn] at hc
    obtain ⟨q,hq,hqe⟩ := hc
    have he : (⟨q.val,pointLocal_le q.property⟩ : pointParabolic) =
        ⁅x,⟨l.val,pointLocal_le l.property⟩⁆ := Subtype.ext hqe
    have hh : pointParabolicQuotient ⁅x,⟨l.val,pointLocal_le l.property⟩⁆ = 1 := by
      rw [← he]
      exact hq
    rw [map_commutatorElement,pointParabolicQuotient_local] at hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  simpa only [Theory.PSL2.sl2_center_eq_bot,mem_bot] using hz

/-- The stabilizer of the two original opposite points, in the centralizer
of the local Levi quotient, is contained in the original opposite pair. -/
theorem mem_pair_of_local_quotient_centralizing {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n) (x : Sp F)
    (hp : x ∈ pointParabolic)
    (ho : x ∈ stabilizer (F ∙ (Pi.single (.inr 0) 1 : Vector F)))
    (hc : ∀ l ∈ pointLocal (F := F), ⁅x,l⁆ ∈ pointLocal.pCoreIn 2) : x ∈ pair := by
  obtain ⟨s,hs⟩ := scalar_of_quotient_eq_one ⟨x,hp⟩
    (quotient_eq_one_of_commutators hF hn ⟨x,hp⟩ hc) ho
  change x = diagonalTorus s 1 at hs
  rw [hs]
  exact diagonal_mem_pair s

omit [Finite F] in
/-- The standard opposition takes the point to its opposite coordinate line. -/
theorem opposition_point_image :
    (point F).map (toLinear TwoConjugate.opposition).toLinearMap =
      F ∙ (Pi.single (.inr 0) 1 : Vector F) := by
  rw [point,Submodule.map_span,Set.image_singleton]
  congr 2
  change (TwoConjugate.opposition (F := F)) • e (F := F) 0 = _
  rw [TwoConjugate.opposition_apply]
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e]

omit [Finite F] [CharP F 2] in
private theorem unmove_stabilizer (U : Submodule F (Vector F)) (g x : Sp F)
    (hx : x ∈ stabilizer (U.map (toLinear g).toLinearMap)) :
    g⁻¹ * x * g ∈ stabilizer U := by
  apply (mem_stabilizer_iff _ _).mpr
  intro v hv
  obtain ⟨w,hw,he⟩ := (mem_stabilizer_iff _ _).mp hx (g • v) ⟨v,hv,rfl⟩
  have he' : g⁻¹ • (x • (g • v)) = w := by
    rw [← show g • w = x • (g • v) from he,inv_smul_smul]
  change (g⁻¹ * x * g) • v ∈ U
  rw [mul_smul,mul_smul,he']
  exact hw

/-- The pair criterion in an arbitrary symplectic frame, retaining the
literal local two-core and commutators. -/
theorem mem_conjugate_pair_of_local_quotient_centralizing {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n) (g x : Sp F)
    (hp : x ∈ stabilizer ((point F).map (toLinear g).toLinearMap))
    (ho : x ∈ stabilizer ((F ∙ (Pi.single (.inr 0) 1 : Vector F)).map
      (toLinear g).toLinearMap))
    (hc : ∀ l ∈ pointLocal.map (MulAut.conj g).toMonoidHom,
      ⁅x,l⁆ ∈ (pointLocal.map (MulAut.conj g).toMonoidHom).pCoreIn 2) :
    x ∈ pair.map (MulAut.conj g).toMonoidHom := by
  refine ⟨g⁻¹ * x * g,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
  apply mem_pair_of_local_quotient_centralizing hF hn _
    (unmove_stabilizer _ g x hp) (unmove_stabilizer _ g x ho)
  intro l hl
  have hh := hc ((MulAut.conj g) l) (mem_map_of_mem _ hl)
  rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective] at hh
  obtain ⟨z,hz,he⟩ := hh
  have hcomm : (MulAut.conj g) ⁅g⁻¹ * x * g,l⁆ = ⁅x,(MulAut.conj g) l⁆ := by
    rw [map_commutatorElement]
    simp [MulAut.conj_apply,mul_assoc]
  have he' : z = ⁅g⁻¹ * x * g,l⁆ := (MulAut.conj g).injective (he.trans hcomm.symm)
  rwa [← he']

end Theory.SpecificGroups.SymplecticFour.OppositeLongRootPair
