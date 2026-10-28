module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.Setup
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus

/-!
# The normalizer-invariant subgroups of the two symplectic radicals

The actual central quotients of the point and plane radicals are natural
SL₂ modules, irreducible even as additive groups. For a normal subgroup N
of the determinant-one local group inside its radical Q, apply this
irreducibility to N joined with the relative center. Since `[Q,L] = Q`,
a subgroup surjecting onto the central quotient must be Q itself.
Otherwise N is contained in the distinguished root, identified using the
original point coordinates or alternating symmetric-matrix coordinates.

The full parabolic torus acts transitively on the nonidentity elements of
each distinguished root: the weights are a² for root 0 and ab for root 4.
Thus every nontrivial subgroup of either radical normalized by its full
normalizer is the full central root or the full radical. Normality is used
only inside the corresponding local group, never in the ambient Sp₄(F).

Source: Guralnick--Malle, *Classification of 2F-modules II*, Proposition 6.2
part 1A, author manuscript pp.38--39; Aschbacher--Smith K.3.4, printed
pp.456--457 of the combined manuscript of 1 March 2004.
-/

public section
open Matrix Subgroup Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree

private theorem natural_normal_le_center_or_eq
    {F L : Type*} [Field F] [Group L] {Q : Subgroup L} [Q.Normal]
    (d : NaturalExtension (F := F) Q) (N : Subgroup L) [N.Normal] (hN : N ≤ Q) :
    N ≤ center L ∨ N = Q := by
  rcases d.invariant_interval (N ⊔ (Q ⊓ center L)) le_sup_right
    (sup_le hN inf_le_left) with hc | hfull
  · exact Or.inl (le_sup_left.trans (hc.le.trans inf_le_right))
  · right
    apply le_antisymm hN
    rw [← d.commutator_eq]
    apply commutator_le.mpr
    intro q hq l _
    rw [← hfull] at hq
    obtain ⟨n,hn,z,hz,rfl⟩ := mem_sup_of_normal_left.mp hq
    have hzcomm : ⁅z,l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp hz.2 l).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hzcomm, mul_one, mul_inv_cancel, one_mul]
    exact (commutator_le_left N ⊤) (commutator_mem_commutator hn (mem_top l))

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem point_central_root (q : pointRadical (F := F))
    (hq : q.val ∈ center (pointLocal (F := F))) : q.val.val ∈ centralRoot false := by
  obtain ⟨z,hz⟩ := (pointRadical_mem_center_iff q).mp hq
  apply (RootSubgroup.mem_group_iff 0 _).mpr
  refine ⟨z, ?_⟩
  rw [hz]
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, rootElement, rootMatrix,
      Matrix.fromBlocks, Matrix.single]

omit [Finite F] in
private theorem plane_central_root (q : Plane.radical (F := F))
    (hq : q.val ∈ center (planeLocal (F := F))) : q.val.val ∈ centralRoot true := by
  obtain ⟨z,hz⟩ := (Plane.mem_center_subgroupOf_iff_alternating q).mp hq
  apply (RootSubgroup.mem_group_iff 4 _).mpr
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [Plane.radical_matrix q]
  change rootMatrix 4 z = fromBlocks 1 (Plane.radicalEquiv q).toAdd.val 0 1
  rw [hz]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.single]

/-- The local natural quotient and commutator calculation reduce a normalized
radical subgroup to the central root or the full radical. -/
theorem normalized_le_centralRoot_or_eq_radical {r : ℕ}
    (hF : Nat.card F = 2 ^ r) (hr : 1 < r)
    (i : Bool) (B : Subgroup (Sp F)) (hBQ : B ≤ radical i)
    (hBN : normalizer (radical (F := F) i : Set (Sp F)) ≤ normalizer (B : Set (Sp F))) :
    B ≤ centralRoot i ∨ B = radical i := by
  cases i
  · change B ≤ pointRadicalAmbient at hBQ
    change normalizer (pointRadicalAmbient (F := F) : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) at hBN
    have hBL : B ≤ pointLocal := hBQ.trans (map_subtype_le _)
    have hLN : pointLocal (F := F) ≤ normalizer (B : Set (Sp F)) := by
      rw [pointRadicalAmbient_normalizer hF hr] at hBN
      exact pointLocal_le.trans hBN
    let : (B.subgroupOf pointLocal).Normal :=
      (normal_subgroupOf_iff_le_normalizer hBL).mpr hLN
    have hsub : B.subgroupOf pointLocal ≤ pointRadical := by
      have hm := Subgroup.comap_mono (f := pointLocal.subtype) hBQ
      rwa [comap_map_eq_self_of_injective pointLocal.subtype_injective] at hm
    rcases natural_normal_le_center_or_eq (pointNaturalExtension hF hr) _ hsub with hc | he
    · left
      intro x hx
      exact point_central_root ⟨⟨x,hBL hx⟩,hsub hx⟩ (hc hx)
    · right
      have hm := congrArg (Subgroup.map pointLocal.subtype) he
      rwa [map_subgroupOf_eq_of_le hBL] at hm
  · change B ≤ planeRadicalAmbient at hBQ
    change normalizer (planeRadicalAmbient (F := F) : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) at hBN
    have hBL : B ≤ planeLocal := hBQ.trans (map_subtype_le _)
    have hLN : planeLocal (F := F) ≤ normalizer (B : Set (Sp F)) := by
      rw [planeRadicalAmbient_normalizer hF hr] at hBN
      exact planeLocal_le.trans hBN
    let : (B.subgroupOf planeLocal).Normal :=
      (normal_subgroupOf_iff_le_normalizer hBL).mpr hLN
    have hsub : B.subgroupOf planeLocal ≤ Plane.radical := by
      have hm := Subgroup.comap_mono (f := planeLocal.subtype) hBQ
      rwa [comap_map_eq_self_of_injective planeLocal.subtype_injective] at hm
    rcases natural_normal_le_center_or_eq (planeNaturalExtension hF hr) _ hsub with hc | he
    · left
      intro x hx
      exact plane_central_root ⟨⟨x,hBL hx⟩,hsub hx⟩ (hc hx)
    · right
      have hm := congrArg (Subgroup.map planeLocal.subtype) he
      rwa [map_subgroupOf_eq_of_le hBL] at hm

omit [Finite F] in
private theorem torus_root (i : Bool) (a : Fˣ) (s : F) :
    diagonalTorus a 1 * rootElement (if i then 4 else 0) s * (diagonalTorus a 1)⁻¹ =
      rootElement (if i then 4 else 0) ((if i then (a : F) else (a : F)^2) * s) := by
  cases i
  · simpa [CentralRootGeometry.diagonalTorusHom_apply, CentralRootGeometry.parameter_apply,
      RootSubgroup.element_zero] using
      CentralRootGeometry.diagonalTorus_weights (a,1) s 0
  · simpa [CentralRootGeometry.diagonalTorusHom_apply, CentralRootGeometry.parameter_apply,
      RootSubgroup.element_zero] using
      CentralRootGeometry.diagonalTorus_weights (a,1) 0 s

private theorem torus_normalizes_radical {r : ℕ}
    (hF : Nat.card F = 2 ^ r) (hr : 1 < r) (i : Bool) (a : Fˣ) :
    diagonalTorus a 1 ∈ normalizer (radical (F := F) i : Set (Sp F)) := by
  have hb := diagonalTorus_mem_borel a 1
  cases i
  · change _ ∈ normalizer (pointRadicalAmbient (F := F) : Set (Sp F))
    rw [pointRadicalAmbient_normalizer hF hr]
    exact hb.1
  · change _ ∈ normalizer (planeRadicalAmbient (F := F) : Set (Sp F))
    rw [planeRadicalAmbient_normalizer hF hr]
    exact hb.2

private theorem root_transitive {r : ℕ}
    (hF : Nat.card F = 2 ^ r) (hr : 1 < r) (i : Bool)
    {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ g ∈ normalizer (radical (F := F) i : Set (Sp F)),
      g * rootElement (if i then 4 else 0) s * g⁻¹ = rootElement (if i then 4 else 0) t := by
  have hp : ∃ a : Fˣ, (if i then (a : F) else (a : F)^2) * s = t := by
    cases i
    · let c := (frobeniusEquiv F 2).symm (t / s)
      have hc : c ^ 2 = t / s := frobeniusEquiv_symm_pow_p F 2 _
      have hc0 : c ≠ 0 := by
        intro hz
        apply div_ne_zero ht hs
        rw [← hc, hz]
        simp
      exact ⟨Units.mk0 c hc0, by simpa only [Bool.false_eq_true, ↓reduceIte,
        Units.val_mk0, hc] using div_mul_cancel₀ t hs⟩
    · exact ⟨Units.mk0 (t / s) (div_ne_zero ht hs), div_mul_cancel₀ t hs⟩
  obtain ⟨a,ha⟩ := hp
  refine ⟨diagonalTorus a 1, torus_normalizes_radical hF hr i a, ?_⟩
  rw [torus_root, ha]

/-- A nontrivial subgroup invariant under the full radical normalizer is
exactly the distinguished central root or the whole radical, for either root length. -/
theorem normalized_radical_subgroup {r : ℕ}
    (hF : Nat.card F = 2 ^ r) (hr : 1 < r)
    (i : Bool) (B : Subgroup (Sp F)) (hBQ : B ≤ radical i) (hB : B ≠ ⊥)
    (hBN : normalizer (radical (F := F) i : Set (Sp F)) ≤ normalizer (B : Set (Sp F))) :
    B = centralRoot i ∨ B = radical i := by
  rcases normalized_le_centralRoot_or_eq_radical hF hr i B hBQ hBN with hc | he
  · left
    apply le_antisymm hc
    rcases B.bot_or_exists_ne_one with hz | ⟨x,hx,hx1⟩
    · exact (hB hz).elim
    obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff (if i then 4 else 0) x).mp (hc hx)
    have hs : s ≠ 0 := by
      intro hz
      apply hx1
      rw [hz, RootSubgroup.element_zero]
    intro y hy
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff (if i then 4 else 0) y).mp hy
    by_cases ht : t = 0
    · rw [ht, RootSubgroup.element_zero]
      exact B.one_mem
    obtain ⟨g,hg,he⟩ := root_transitive hF hr i hs ht
    rw [← he]
    exact (mem_normalizer_iff.mp (hBN hg) _).mp hx
  · exact Or.inr he

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
