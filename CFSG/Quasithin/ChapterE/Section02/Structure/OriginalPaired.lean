module
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedMaximal
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedCore
public import Theory.GroupTheory.QuotientIntersection

/-!
# The original exchanged maximal product

The proved paired-core theorem identifies J with O₂(H), hence the kernel
lies in the original Sylow subgroup. Apply the simple-component product
theorem in H/J and lift its conjugator through the prescribed Sylow map.
The maximal intersection commutes with this quotient, and the kernel can
be absorbed in the final Sylow factor. The output retains the source's
right-conjugation convention on the original C-component.

Source: Aschbacher–Smith E.2.2(1), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

omit [Finite H] in
private theorem map_conjugate {A : Type*} [Group A]
    (f : H →* A) (K : Subgroup H) (t : H) :
    (K.map (MulAut.conj t).toMonoidHom).map f =
      (K.map f).map (MulAut.conj (f t)).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

/-- The full original paired maximal product, with its actual Sylow conjugator. -/
theorem source_original_exchanged_product
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) {K : Subgroup H} (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K)) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hn : ¬ K.Normal) :
    ∃ t ∈ (T : Subgroup H), K ≠ K.conjBy t⁻¹ ∧
      (ChapterB.minimalParabolicMax T hP : Set H) =
        (ChapterB.minimalParabolicMax T hP ⊓ K : Subgroup H) *
          (((ChapterB.minimalParabolicMax T hP ⊓ K).conjBy t⁻¹ : Subgroup H) : Set H) * (T : Set H) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hq := QuotientGroup.mk'_surjective J
  let S := T.mapSurjective hq
  have hJ := PairedCore.source hA hH T hP hs hK hqK hgen hn
  have hkerT : q.ker ≤ (T : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    change ChapterB.minimalParabolicCore T hP ≤ (T : Subgroup H)
    rw [hJ]
    exact pCore_isPGroup.le_sylow_of_normal T
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hi := source_component_simple_image T hP hs K hK hgen
  let := hi.1
  have hnD : ¬ (K.map q).Normal := fun hd => hn (cComponent_normal_of_quotient_normal hK J hd)
  have hmin := (source_star_minimal_core_free T hP).1
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q hq (by rw [QuotientGroup.ker_mk'])).symm
  obtain ⟨s,hne,hprod⟩ := source_paired_maximal_product
    (source_star_sqtk (hA H) hH T hP hs).stronglyQuasithin S hmin hi.2.1 hi.2.2.2 hnD
  rw [hmax] at hprod
  obtain ⟨t,ht,hqt⟩ : ∃ t : H, t ∈ (T : Subgroup H) ∧ q t = (s : H ⧸ J) := s.property
  let B := M ⊓ K
  have hkerM : q.ker ≤ M := hkerT.trans (ChapterB.minimalParabolicMax_spec T hP).2
  have hB : B.map q = M.map q ⊓ K.map q := by
    rw [show B = K ⊓ M from inf_comm M K,map_inf_of_ker_le q K M hkerM,inf_comm]
  have htne : K.map (MulAut.conj t).toMonoidHom ≠ K := by
    intro he
    apply hne
    rw [←hqt,←map_conjugate,he]
  refine ⟨t⁻¹,(T : Subgroup H).inv_mem ht,?_,?_⟩
  · rw [inv_inv]
    change K ≠ K.map (MulAut.conj t).toMonoidHom
    exact htne.symm
  · change (M : Set H) = (B : Set H) * ((B.conjBy (t⁻¹)⁻¹ : Subgroup H) : Set H) * (T : Set H)
    rw [inv_inv]
    ext x
    constructor
    · intro hx
      have hqx : q x ∈ (M.map q : Set (H ⧸ J)) := mem_map_of_mem q hx
      rw [hprod] at hqx
      obtain ⟨a,⟨b,hb,c,hc,hbc⟩,r,hr,har⟩ := hqx
      rw [←hB] at hb hc
      obtain ⟨k,hk,hqk⟩ := hb
      have hcmap : c ∈ (B.conjBy t).map q := by
        rw [show B.conjBy t = B.map (MulAut.conj t).toMonoidHom from rfl,
          map_conjugate,hqt]
        exact hc
      obtain ⟨d,hd,hqd⟩ := hcmap
      obtain ⟨v,hv,hqv⟩ := hr
      change b*c = a at hbc
      change a*r = q x at har
      have he : q (k*d*v) = q x := by rw [map_mul,map_mul,hqk,hqd,hqv,hbc,har]
      have heker : (k*d*v)⁻¹*x ∈ q.ker := by
        rw [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
      let w := v * ((k*d*v)⁻¹*x)
      have hw : w ∈ (T : Subgroup H) := (T : Subgroup H).mul_mem hv (hkerT heker)
      refine Set.mem_mul.mpr ⟨k*d,Set.mem_mul.mpr ⟨k,hk,d,hd,rfl⟩,w,hw,?_⟩
      dsimp [w]
      group
    · rintro ⟨a,⟨b,hb,c,hc,rfl⟩,v,hv,rfl⟩
      have hcM : c ∈ M := by
        obtain ⟨d,hd,rfl⟩ := hc
        exact (M.le_normalizer ((ChapterB.minimalParabolicMax_spec T hP).2 ht) d).mp hd.1
      exact M.mul_mem (M.mul_mem hb.1 hcM) ((ChapterB.minimalParabolicMax_spec T hP).2 hv)
end CFSG.Quasithin.ChapterE.Structure
