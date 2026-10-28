module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.Setup
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates

/-!
# Elementary actors lie in a symplectic parabolic radical

The square formula in the actual standard Sylow coordinates gives `b*v = 0`
for every involution. Applying this equation to products shows that an
entire elementary subgroup has `b = 0` throughout or `v = 0` throughout.
These two coordinate families are embedded in the plane and point radicals,
respectively. Sylow conjugacy then places every elementary actor in one of
the two radicals using an actual inner automorphism of Sp₄(F).

Source: Guralnick--Malle, *Classification of 2F-modules II*, Proposition 6.2
part 1A, author manuscript pp.38--39; Aschbacher--Smith K.3.4, printed
pp.456--457 of the combined manuscript of 1 March 2004.
-/

public section
open Matrix Subgroup Theory.SpecificGroups.SymplecticFour
open CentralRootGeometry
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def b (x : unipotent (F := F)) : F := x.val.val (.inl 0) (.inl 1)
private def v (x : unipotent (F := F)) : F := x.val.val (.inl 1) (.inr 1)

omit [Finite F] in
private theorem bv_element (b₀ u w v₀ : F) :
    b (element b₀ u w v₀) = b₀ ∧ v (element b₀ u w v₀) = v₀ := by
  simp only [b, v, element_matrix]
  exact ⟨rfl, rfl⟩

private theorem bv_mul (x y : unipotent (F := F)) :
    b (x * y) = b x + b y ∧ v (x * y) = v x + v y := by
  obtain ⟨⟨b₀,u,w,v₀⟩,rfl⟩ := element_surjective x
  obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
  rw [element_mul]
  exact ⟨by rw [(bv_element ..).1, (bv_element ..).1, (bv_element ..).1],
    by rw [(bv_element ..).2, (bv_element ..).2, (bv_element ..).2]⟩

private theorem bv_square (x : unipotent (F := F)) (hx : x ^ 2 = 1) : b x * v x = 0 := by
  obtain ⟨⟨b₀,u,w,v₀⟩,rfl⟩ := element_surjective x
  rw [(bv_element ..).1, (bv_element ..).2]
  rw [element_square, theta, ← element_zero] at hx
  exact ((element_eq_iff ..).mp hx).2.2.1

private theorem coordinate_alternative
    (A : Subgroup (unipotent (F := F))) [IsElementaryAbelian 2 A] :
    (∀ a : A, b a.val = 0) ∨ (∀ a : A, v a.val = 0) := by
  have hs (a : A) : b a.val * v a.val = 0 := bv_square a.val
    (congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a))
  by_cases hb : ∀ a : A, b a.val = 0
  · exact Or.inl hb
  · push Not at hb
    obtain ⟨a, ha⟩ := hb
    have hav : v a.val = 0 := (mul_eq_zero.mp (hs a)).resolve_left ha
    refine Or.inr (fun c => ?_)
    by_cases hc : b c.val = 0
    · have hac := hs (a * c)
      change b (a.val * c.val) * v (a.val * c.val) = 0 at hac
      rw [(bv_mul ..).1, (bv_mul ..).2, hc, hav, add_zero, zero_add] at hac
      exact (mul_eq_zero.mp hac).resolve_left ha
    · exact (mul_eq_zero.mp (hs c)).resolve_left hc

omit [Finite F] in
private theorem element_point (b₀ u w : F) :
    (element b₀ u w 0).val = (pointRadicalElement w b₀ u).val := by
  apply Subtype.ext
  rw [element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, Matrix.fromBlocks]

omit [Finite F] in
private theorem element_plane (u w v₀ : F) :
    (element 0 u w v₀).val ∈ planeRadicalAmbient := by
  let B : Plane.symmetricMatrices F := ⟨!![u,w;w,v₀], by
    ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  have he : (element 0 u w v₀).val = (Plane.shear B).val := by
    apply Subtype.ext
    rw [element_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Plane.shear, Plane.shearSp, B, Matrix.fromBlocks]
  rw [he]
  exact mem_map_of_mem planeLocal.subtype
    (show Plane.shear B ∈ Plane.radical from Plane.quotientMap_shear B)

/-- Inside the standard Sylow, every elementary subgroup lies in one of the
two actual embedded radicals. -/
theorem elementary_unipotent_le_radical
    (A : Subgroup (Sp F)) (hAU : A ≤ unipotent) [IsElementaryAbelian 2 A] :
    ∃ i : Bool, A ≤ radical i := by
  let : IsElementaryAbelian 2 (A.subgroupOf unipotent) := IsElementaryAbelian.subgroupOf hAU
  rcases coordinate_alternative (A.subgroupOf unipotent) with hb | hv
  · refine ⟨true, ?_⟩
    intro x hx
    obtain ⟨⟨b₀,u,w,v₀⟩,he⟩ := element_surjective (⟨x,hAU hx⟩ : unipotent)
    have hz := hb ⟨⟨x,hAU hx⟩,hx⟩
    change b ⟨x,hAU hx⟩ = 0 at hz
    rw [← he, (bv_element ..).1] at hz
    change b₀ = 0 at hz
    subst b₀
    change x ∈ planeRadicalAmbient
    have hx' : (element 0 u w v₀).val = x := congrArg Subtype.val he
    rw [← hx']
    exact element_plane u w v₀
  · refine ⟨false, ?_⟩
    intro x hx
    obtain ⟨⟨b₀,u,w,v₀⟩,he⟩ := element_surjective (⟨x,hAU hx⟩ : unipotent)
    have hz := hv ⟨⟨x,hAU hx⟩,hx⟩
    change v ⟨x,hAU hx⟩ = 0 at hz
    rw [← he, (bv_element ..).2] at hz
    change v₀ = 0 at hz
    subst v₀
    change x ∈ pointRadicalAmbient
    have hx' : (element b₀ u w 0).val = x := congrArg Subtype.val he
    rw [← hx', element_point]
    exact mem_map_of_mem _ (pointRadicalElement_mem w b₀ u)

/-- Every elementary actor is carried into a standard radical by an actual
inner automorphism. Placement also holds at the binary parameter r = 1. -/
theorem elementary_placement {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r)
    (A : Subgroup (Sp F)) (hA : Representation.BinaryOffender.IsElementaryTwo A) :
    ∃ (g : Sp F) (i : Bool), A.map (MulAut.conj g).toMonoidHom ≤ radical i := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hr)
  have hAU : A.map (MulAut.conj g).toMonoidHom ≤ unipotent := by
    have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAS
    have he : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
      congrArg (fun T : Sylow 2 (Sp F) => (T : Subgroup (Sp F))) hg
    exact he ▸ hm
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  obtain ⟨i,hi⟩ := elementary_unipotent_le_radical _ hAU
  exact ⟨g,i,hi⟩

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
