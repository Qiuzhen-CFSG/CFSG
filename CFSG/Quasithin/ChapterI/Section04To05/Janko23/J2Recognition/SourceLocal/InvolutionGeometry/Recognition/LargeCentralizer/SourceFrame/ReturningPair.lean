module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Contracts
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The returning pair in the J₂ source geometry

Failure of weak closure supplies a conjugate of z in Q distinct from z.
These two commuting involutions generate the source four-group E. We keep
the conjugator, both literal core intersections and their join R marked.
The four-group is contained in Q and in the image of the center of R.
Equality with that center, the order of R and its complement action are
the additional assertions of 46.2–46.3, not part of the returning-pair input.

Source: Aschbacher, *Sporadic Groups* (1994), §46, printed pp.250–251.
Our conjugation convention is g z g⁻¹ throughout.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame

variable {G : Type*} [Group G] [Finite G]

structure ReturningPair (D : Seed G) where
  g : G
  mem_core : g * D.z * g⁻¹ ∈ ambientCore D.z
  ne : g * D.z * g⁻¹ ≠ D.z

theorem exists_returningPair (D : Seed G) : Nonempty (ReturningPair D) := by
  obtain ⟨u, hu, hzu, hne⟩ := D.localType.exists_returning_conjugate
  obtain ⟨g, rfl⟩ := isConj_iff.mp hzu
  exact ⟨⟨g, hu, hne⟩⟩

namespace ReturningPair

variable {D : Seed G} (P : ReturningPair D)

def u : G := P.g * D.z * P.g⁻¹
def E : Subgroup G := zpowers D.z ⊔ zpowers P.u
def conjugateCore : Subgroup G := (ambientCore D.z).map (MulAut.conj P.g).toMonoidHom
def leftCore : Subgroup G := ambientCore D.z ⊓ involutionCentralizer P.u
def rightCore : Subgroup G := P.conjugateCore ⊓ involutionCentralizer D.z
def R : Subgroup G := P.leftCore ⊔ P.rightCore

theorem u_order : orderOf P.u = 2 :=
  ((MulAut.conj P.g).orderOf_eq D.z).trans D.localType.involution

theorem commute : Commute D.z P.u :=
  (mem_centralizer_singleton_iff.mp (ambientCore_le D.z P.mem_core)).symm

theorem E_le_core : P.E ≤ ambientCore D.z :=
  sup_le (zpowers_le.mpr HTypeAt.involution_mem_core) (zpowers_le.mpr P.mem_core)

theorem z_mem_E : D.z ∈ P.E := mem_sup_left (mem_zpowers D.z)
theorem u_mem_E : P.u ∈ P.E := mem_sup_right (mem_zpowers P.u)

theorem E_elementary : IsElementaryAbelian 2 P.E := by
  let : IsElementaryAbelian 2 (zpowers D.z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (D.localType.involution ▸ pow_orderOf_eq_one D.z)
  let : IsElementaryAbelian 2 (zpowers P.u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (P.u_order ▸ pow_orderOf_eq_one P.u)
  apply IsElementaryAbelian.sup_of_le_centralizer
  apply zpowers_le.mpr
  intro x hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  exact (P.commute.zpow_left n).eq

theorem E_card : Nat.card P.E = 4 := by
  classical
  have hout : P.u ∉ zpowers D.z := by
    intro hu
    rw [mem_zpowers_iff_mem_range_orderOf, D.localType.involution] at hu
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hu
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · have h1 : P.u = 1 := by simpa using he.symm
      have := P.u_order
      simp [h1] at this
    · exact P.ne (by simpa only [pow_one, u] using he.symm)
  have hnorm : P.u ∈ normalizer (zpowers D.z : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact (P.commute.zpow_left n).eq
  rw [E, card_sup_zpowers_of_normalizing_involution _ _
    (P.u_order ▸ pow_orderOf_eq_one P.u) hout hnorm,
    Nat.card_zpowers, D.localType.involution]

theorem conjugateCore_le : P.conjugateCore ≤ involutionCentralizer P.u := by
  rintro _ ⟨q, hq, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  exact (map_mul (MulAut.conj P.g) q D.z).symm.trans
    ((congrArg (MulAut.conj P.g)
      (mem_centralizer_singleton_iff.mp (ambientCore_le D.z hq))).trans
      (map_mul (MulAut.conj P.g) D.z q))

theorem conjugate_centralizer :
    (involutionCentralizer D.z).map (MulAut.conj P.g).toMonoidHom =
      involutionCentralizer P.u := by
  let e := MulAut.conj P.g
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, e, u,
      MulAut.conj_apply] using
      map_centralizer_le_centralizer_image ({D.z} : Set G) e.toMonoidHom
  · intro x hx
    refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply, e, u, MulAut.conj_apply] using
      mem_centralizer_singleton_iff.mp hx

theorem normalizer_conjugateCore :
    normalizer (P.conjugateCore : Set G) = involutionCentralizer P.u := by
  rw [conjugateCore, ← map_equiv_normalizer_eq, D.localType.normalizer_core]
  exact P.conjugate_centralizer

/-- The join is the actual product in the source definition of R. -/
theorem R_coe : (P.R : Set G) = (P.leftCore : Set G) * (P.rightCore : Set G) := by
  apply coe_mul_of_left_le_normalizer_right
  apply le_trans _ inf_normalizer_le_normalizer_inf
  apply le_inf
  · rw [P.normalizer_conjugateCore]
    exact inf_le_right
  · exact (inf_le_left.trans (ambientCore_le D.z)).trans le_normalizer

theorem R_le_double_centralizer :
    P.R ≤ involutionCentralizer D.z ⊓ involutionCentralizer P.u :=
  sup_le (le_inf (inf_le_left.trans (ambientCore_le D.z)) inf_le_right)
    (le_inf inf_le_right (inf_le_left.trans P.conjugateCore_le))

theorem E_le_R : P.E ≤ P.R := by
  apply le_sup_of_le_left
  apply le_inf P.E_le_core
  apply sup_le
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr P.commute.eq)
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

theorem E_le_center_image : P.E ≤ (center P.R).map P.R.subtype := by
  have hRC : P.R ≤ centralizer (P.E : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply zpowers_le.mpr
      intro r hr
      exact mem_centralizer_singleton_iff.mp (P.R_le_double_centralizer hr).1
    · apply zpowers_le.mpr
      intro r hr
      exact mem_centralizer_singleton_iff.mp (P.R_le_double_centralizer hr).2
  intro e he
  refine mem_map.mpr ⟨⟨e, P.E_le_R he⟩, mem_center_iff.mpr ?_, rfl⟩
  intro r
  exact Subtype.ext (hRC r.property e he).symm

end ReturningPair

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
