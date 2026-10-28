module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter
import all Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter

/-!
# Full centralizers of unitary-four long roots

A nonidentity element in the point-residual center has matrix I+cE₀₃
with c nonzero. Commutation forces the first column of every centralizing
matrix to preserve the original isotropic line. The characteristic-two
SU₄ projectivization is injective, so the same containment holds in the
actual projective carrier. The original fixed-field torus orbit also
transports through this quotient, retaining the stored field involution.

Source: Aschbacher–Smith F.4.27(4), printed p.288 of `refs/quasithin.pdf`.
The full-extension and original ambient comparisons are in the ChapterF
and Chapter6 unitary source companions.
-/

open Subgroup Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- A nonidentity element of the point residual center has its entire
special-unitary centralizer in the point parabolic. -/
theorem center_centralizer_le (hnt : ∃ u, σ u ≠ u)
    (z : SU F (form F σ hσ))
    (hz : z ∈ (center (localSU F (form F σ hσ))).map
      (localSU F (form F σ hσ)).subtype) (hne : z ≠ 1) :
    centralizer ({z} : Set (SU F (form F σ hσ))) ≤ pointParabolicSU F (form F σ hσ) := by
  obtain ⟨z,hz,rfl⟩ := hz
  obtain ⟨r,hr,hrc⟩ := center_local_to_radical F σ hσ z hz
  let c := coordinatesOfRadical F σ hσ r
  obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt r).mp hrc
  change c.x = 0 at hx
  change c.y = 0 at hy
  have hm : z.val.val.val = radicalMatrix F σ c := by
    have he := congrArg (fun r : radical F σ hσ => r.val.val.val.val)
      ((radicalCoordinatesEquiv F σ hσ).apply_symm_apply r).symm
    change r.val.val.val.val = radicalMatrix F σ c at he
    simpa only [hr] using he
  have hc : c.z ≠ 0 := by
    intro he
    apply hne
    apply Subtype.ext
    apply Units.ext
    change z.val.val.val = (1 : Matrix (Fin 4) (Fin 4) F)
    rw [hm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [radicalMatrix,hx,hy,he]
  intro g hg
  have hcomm := congrArg (fun x : SU F (form F σ hσ) => x.val.val)
    (mem_centralizer_singleton_iff.mp hg)
  change g.val.val * z.val.val.val = z.val.val.val * g.val.val at hcomm
  rw [hm] at hcomm
  apply (mem_pointParabolicSU F _ g).mpr
  have hcol (i : Fin 4) (hi : i ≠ 0) : g.val.val i 0 = 0 := by
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M i 3) hcomm
    apply (mul_eq_zero.mp (show g.val.val i 0 * c.z = 0 from ?_)).resolve_right hc
    fin_cases i
    · exact (hi rfl).elim
    · simpa [radicalMatrix,hx,hy,Matrix.mul_apply,Fin.sum_univ_succ] using he
    · simpa [radicalMatrix,hx,hy,Matrix.mul_apply,Fin.sum_univ_succ] using he
    · simpa [radicalMatrix,hx,hy,Matrix.mul_apply,Fin.sum_univ_succ] using he
  exact ⟨hcol 1 (by decide),hcol 2 (by decide),hcol 3 (by decide)⟩
/-- The injective projective quotient preserves the full long-root
centralizer containment. -/
theorem projective_center_centralizer_le (hnt : ∃ u, σ u ≠ u)
    (z : PSU F (form F σ hσ))
    (hz : z ∈ (center (localPSU F (form F σ hσ))).map
      (localPSU F (form F σ hσ)).subtype) (hne : z ≠ 1) :
    centralizer ({z} : Set (PSU F (form F σ hσ))) ≤
      pointParabolicPSU F (form F σ hσ) := by
  obtain ⟨z,hz,rfl⟩ := hz
  let e := localProjectEquiv F (form F σ hσ)
  let x := e.symm z
  have hx : x ∈ center (localSU F (form F σ hσ)) :=
    (centerCongr e.symm ⟨z,hz⟩).property
  have he : project F (form F σ hσ) x.val = z.val :=
    congrArg Subtype.val (e.apply_symm_apply z)
  intro g hg
  obtain ⟨a,rfl⟩ := project_surjective F (form F σ hσ) g
  refine ⟨a,center_centralizer_le F σ hσ hnt x.val ⟨x,hx,rfl⟩ ?_ ?_,rfl⟩
  · intro hx1
    apply hne
    change z.val = 1
    rw [←he,hx1,map_one]
  · apply mem_centralizer_singleton_iff.mpr
    apply project_injective F (form F σ hσ)
    rw [map_mul,map_mul,he]
    exact mem_centralizer_singleton_iff.mp hg

/-- The actual projective point parabolic is transitive on the nonidentity
center of its vector stabilizer. -/
theorem projective_center_orbit (hnt : ∃ u, σ u ≠ u)
    (z : PSU F (form F σ hσ))
    (hz : z ∈ (center (localPSU F (form F σ hσ))).map
      (localPSU F (form F σ hσ)).subtype) (hz1 : z ≠ 1)
    (w : PSU F (form F σ hσ))
    (hw : w ∈ (center (localPSU F (form F σ hσ))).map
      (localPSU F (form F σ hσ)).subtype) (hw1 : w ≠ 1) :
    ∃ g ∈ pointParabolicPSU F (form F σ hσ), w = g*z*g⁻¹ := by
  obtain ⟨z,hz,rfl⟩ := hz
  obtain ⟨w,hw,rfl⟩ := hw
  let e := localProjectEquiv F (form F σ hσ)
  let x := e.symm z
  let y := e.symm w
  have hx : x ∈ center (localSU F (form F σ hσ)) :=
    (centerCongr e.symm ⟨z,hz⟩).property
  have hy : y ∈ center (localSU F (form F σ hσ)) :=
    (centerCongr e.symm ⟨w,hw⟩).property
  have he : project F (form F σ hσ) x.val = z.val :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hf : project F (form F σ hσ) y.val = w.val :=
    congrArg Subtype.val (e.apply_symm_apply w)
  have hx1 : x.val ≠ 1 := fun hh => hz1 (he.symm.trans (by rw [hh,map_one]))
  have hy1 : y.val ≠ 1 := fun hh => hw1 (hf.symm.trans (by rw [hh,map_one]))
  obtain ⟨g,hg,hconj⟩ := center_orbit F σ hσ hnt x.val ⟨x,hx,rfl⟩ hx1
    y.val ⟨y,hy,rfl⟩ hy1
  refine ⟨project F (form F σ hσ) g,mem_map_of_mem _ hg,?_⟩
  have hh := congrArg (project F (form F σ hσ)) hconj
  change w.val = project F (form F σ hσ) g * z.val * (project F (form F σ hσ) g)⁻¹
  simpa only [map_mul,map_inv,he,hf] using hh
end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCenter
