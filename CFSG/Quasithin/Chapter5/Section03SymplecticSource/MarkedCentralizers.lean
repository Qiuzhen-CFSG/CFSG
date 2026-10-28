module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Paths
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.MarkedCentralizers
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantParabolicPair
public import Theory.SpecificGroups.SymplecticFour.SuzukiBorelPlacement

/-!
# Full centralizers in a genuine symplectic extension

The exact inner intersections and inner-times-middle factorization identify
the two marked endpoints as full parabolic stabilizers. An automorphism
fixing a root element preserves its native centralizer and hence the
corresponding parabolic. An automorphism fixing a nonidentity Sylow square
preserves the Sylow and both parabolics. These facts put the three full
extension centralizers in the prescribed endpoints or whole middle,
including every outer actor.

Source: Aschbacher--Smith F.4.39,42--43, printed pp.294--296 of
refs/quasithin.pdf, in the symplectic specialization of 5.3.2--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.Chapter5.Section03SymplecticSource
open CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem inner_apply (a : MulAut (Sp F)) (x : Sp F) :
    MulAut.conj (a x)=a*MulAut.conj x*a⁻¹ := by
  ext y
  simp

private theorem fixes_native_of_mem (M : Subgroup (MulAut (Sp F)))
    (P : Subgroup (Sp F)) (hMP : M⊓inner F=P.map MulAut.conj)
    (a : MulAut (Sp F)) (ha : a∈M) : P.map a.toMonoidHom=P := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have hxM : MulAut.conj x∈M := (hMP.ge (mem_map_of_mem MulAut.conj hx)).1
    have hh : MulAut.conj (a x)∈M⊓inner F :=
      ⟨inner_apply a x ▸ M.mul_mem (M.mul_mem ha hxM) (M.inv_mem ha),⟨a x,rfl⟩⟩
    rw [hMP] at hh
    obtain ⟨y,hy,he⟩ := hh
    exact SourceExtension.inner_injective he ▸ hy
  · rw [card_map_of_injective a.injective]

private theorem mem_of_fixes_native (E : SourceExtension F)
    (M : Subgroup (MulAut (Sp F))) (P : Subgroup (Sp F))
    (hMP : M⊓inner F=P.map MulAut.conj) (hDM : E.middle≤M)
    (hself : normalizer (P : Set (Sp F))≤P)
    (a : E.carrier) (ha : P.map a.val.toMonoidHom=P) : a.val∈M := by
  obtain ⟨g,b,hb,he⟩ := E.factor a.val a.property
  have hbP := fixes_native_of_mem M P hMP b (hDM hb)
  have hg : g∈P := by
    apply hself
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      P.map (MulAut.conj g).toMonoidHom =
          (P.map b.toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [hbP]
      _ = P := by
        rw [map_map]
        change P.map (MulAut.conj g*b).toMonoidHom=P
        rwa [←he]
  have hgM : MulAut.conj g∈M := (hMP.ge (mem_map_of_mem MulAut.conj hg)).1
  rw [he]
  exact M.mul_mem hgM (hDM hb)

private theorem point_parabolic_self {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    normalizer (pointParabolic (F := F) : Set (Sp F))≤pointParabolic := by
  intro g hg
  have hl := DiagramAutomorphisms.pointLocal_map hF hn (MulAut.conj g)
    (mem_normalizer_iff_map_conj_eq.mp hg)
  rw [←DiagramAutomorphisms.pointLocal_normalizer hF hn]
  exact mem_normalizer_iff_map_conj_eq.mpr hl

private theorem plane_parabolic_self {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n) :
    normalizer (planeParabolic (F := F) : Set (Sp F))≤planeParabolic := by
  intro g hg
  have hl := DiagramAutomorphisms.planeLocal_map hF hn (MulAut.conj g)
    (mem_normalizer_iff_map_conj_eq.mp hg)
  rw [←DiagramAutomorphisms.planeLocal_normalizer hF hn]
  exact mem_normalizer_iff_map_conj_eq.mpr hl

/-- The marked left endpoint is the full stabilizer of the native point parabolic. -/
theorem extension_left_iff {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (E : SourceExtension F) (a : E.carrier) :
    a.val∈E.left ↔ pointParabolic.map a.val.toMonoidHom=pointParabolic := by
  exact ⟨fixes_native_of_mem E.left pointParabolic E.left_inner a.val,
    mem_of_fixes_native E E.left pointParabolic E.left_inner inf_le_left
      (point_parabolic_self hF hn) a⟩

/-- The marked right endpoint is the full stabilizer of the native plane parabolic. -/
theorem extension_right_iff {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (E : SourceExtension F) (a : E.carrier) :
    a.val∈E.right ↔ planeParabolic.map a.val.toMonoidHom=planeParabolic := by
  exact ⟨fixes_native_of_mem E.right planeParabolic E.right_inner a.val,
    mem_of_fixes_native E E.right planeParabolic E.right_inner inf_le_right
      (plane_parabolic_self hF hn) a⟩

omit [Finite F] in
private theorem fixes_of_centralizes (E : SourceExtension F) (z : Sp F)
    (a : E.carrier) (ha : a∈centralizer ({E.innerMap z} : Set E.carrier)) : a.val z=z := by
  apply SourceExtension.inner_injective
  have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
  change a.val*MulAut.conj z=MulAut.conj z*a.val at hh
  rw [inner_apply,hh,mul_inv_cancel_right]

/-- The whole extension centralizer of a point-root involution lies in its marked endpoint. -/
theorem extension_point_centralizer {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (E : SourceExtension F) (z : Sp F)
    (hz : z∈(center (pointLocal (F := F))).map pointLocal.subtype) (hne : z≠1) :
    centralizer ({E.innerMap z} : Set E.carrier)≤E.left.subgroupOf E.carrier := by
  intro a ha
  have hfix := fixes_of_centralizes E z a ha
  have hlocal : pointLocal.map a.val.toMonoidHom=pointLocal := by
    rw [←SourceFusionOrder.point_center_element_centralizer hF hn z hz hne,
      CentralizerSmallKernelTransport.map_centralizer,hfix]
  apply (extension_left_iff hF hn E a).mpr
  rw [←DiagramAutomorphisms.pointLocal_normalizer hF hn,map_equiv_normalizer_eq,hlocal]

/-- The whole extension centralizer of a plane-root involution lies in its marked endpoint. -/
theorem extension_plane_centralizer {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (E : SourceExtension F) (z : Sp F)
    (hz : z∈(center (planeLocal (F := F))).map planeLocal.subtype) (hne : z≠1) :
    centralizer ({E.innerMap z} : Set E.carrier)≤E.right.subgroupOf E.carrier := by
  intro a ha
  have hfix := fixes_of_centralizes E z a ha
  have hlocal : planeLocal.map a.val.toMonoidHom=planeLocal := by
    rw [←SourceFusionOrder.plane_center_element_centralizer hF hn z hz hne,
      CentralizerSmallKernelTransport.map_centralizer,hfix]
  apply (extension_right_iff hF hn E a).mpr
  rw [←DiagramAutomorphisms.planeLocal_normalizer hF hn,map_equiv_normalizer_eq,hlocal]

/-- The whole extension centralizer of a nonidentity Sylow square lies in the whole middle. -/
theorem extension_square_centralizer {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (E : SourceExtension F) (z : unipotent (F := F)) (hne : z≠1)
    (hsq : ∃ y : unipotent (F := F), y^2=z) :
    centralizer ({E.innerMap z.val} : Set E.carrier)≤E.middle.subgroupOf E.carrier := by
  obtain ⟨y,hy⟩ := hsq
  have hc : centralizer ({z.val} : Set (Sp F))=unipotent := by
    have hh := centralizer_square_eq_unipotent y (by rwa [hy])
    simpa only [←Subgroup.coe_pow,hy] using hh
  intro a ha
  have hfix := fixes_of_centralizes E z.val a ha
  have hU : unipotent.map a.val.toMonoidHom=unipotent := by
    rw [←hc,CentralizerSmallKernelTransport.map_centralizer,hfix]
  obtain ⟨hl,hr⟩ := DiagramAutomorphisms.parabolic_pair_map_of_unipotent_map
    hF hn a.val (E.preserves_diagram a.val a.property) hU
  exact ⟨(extension_left_iff hF hn E a).mpr hl,(extension_right_iff hF hn E a).mpr hr⟩

end CFSG.Quasithin.Chapter5.Section03SymplecticSource
