module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCoreActor
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramMarkedKernel
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The maximal two-core fixes the component's odd central quotient

The center preimage lies in the marked maximal subgroup. A commutator
with its two-core is therefore a two-element, while its component quotient
lies in the odd center. Coprimality makes the commutator trivial in that
quotient, so the induced automorphism fixes every central element.

The literal original component cover supplies the center-preimage
containment through its marked kernel. This is the source input excluding
the cubic SL₃(4) cover in Aschbacher--Smith 14.2.12, printed p.984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

 theorem core_actor_fixes_quotient_center
    (M K : Subgroup H) [K.Normal]
    (hCM : (centralPreimage (pCore 2 K)).map K.subtype ≤ M)
    (g : H) (hg : g ∈ M.pCoreIn 2)
    (z : K ⧸ pCore 2 K) (hz : z ∈ center (K ⧸ pCore 2 K)) :
    normalQuotientAction K (pCore 2 K) g z = z := by
  let q := QuotientGroup.mk' (pCore 2 K)
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
  have hxC : x ∈ centralPreimage (pCore 2 K) := hz
  have hxM : (x : H) ∈ M := hCM (mem_map_of_mem K.subtype hxC)
  let a := MulAut.conjNormal (H := K) g
  let y : K := a x * x⁻¹
  have hyC : y ∈ centralPreimage (pCore 2 K) :=
    (centralPreimage (pCore 2 K)).mul_mem
      (characteristic_iff_le_comap.mp inferInstance a hxC)
      ((centralPreimage (pCore 2 K)).inv_mem hxC)
  have hyQ : (y : H) ∈ M.pCoreIn 2 := by
    have hxN : (x : H) ∈ normalizer (M.pCoreIn 2 : Set H) :=
      (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))) hxM
    change g * (x : H) * g⁻¹ * (x : H)⁻¹ ∈ M.pCoreIn 2
    rw [mul_assoc g (x : H) g⁻¹, mul_assoc]
    exact (M.pCoreIn 2).mul_mem hg
      ((mem_normalizer_iff.mp hxN g⁻¹).mp ((M.pCoreIn 2).inv_mem hg))
  let P := (M.pCoreIn 2).subgroupOf K
  let J := P.map q
  have hp : IsPGroup 2 J := ((isPGroup_pCoreIn 2 M).comap_subtype).map q
  have hod : Odd (Nat.card (center (K ⧸ pCore 2 K))) :=
    Nat.not_even_iff_odd.mp (by
      rw [even_iff_two_dvd]
      exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2) _ le_rfl)
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : Disjoint J (center (K ⧸ pCore 2 K)) :=
    Subgroup.disjoint_of_coprime_natCard (hn ▸ hod.coprime_two_left.pow_left n)
  have hy1 : q y = 1 := (disjoint_def.mp hd (mem_map_of_mem q hyQ) hyC)
  rw [normalQuotientAction_apply_mk]
  have hh : q (a x) * (q x)⁻¹ = 1 := by
    simpa only [y,map_mul,map_inv] using hy1
  exact mul_inv_eq_one.mp hh

 theorem original_core_actor_fixes_quotient_center
    {D : Type*} [Group D]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* D)
    (g : H) (hg : g ∈ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (z : K ⧸ pCore 2 K) (hz : z ∈ center (K ⧸ pCore 2 K)) :
    normalQuotientAction K (pCore 2 K) g z = z := by
  apply core_actor_fixes_quotient_center (ChapterB.minimalParabolicMax T hP) K _ g hg z hz
  rw [← original_markedParabolicMap_kernel T hP hs K hK hqK hgen e]
  rintro _ ⟨x,hx,rfl⟩
  have hf := MonoidHom.mem_ker.mp hx
  have hq : QuotientGroup.mk' (sourceKernel (ChapterB.minimalParabolicMax T hP)) (x : H) = 1 := by
    have hh := e.injective (hf.trans (map_one e).symm)
    exact congrArg (fun y => y.val) hh
  exact (ChapterB.minimalParabolicMax T hP).normalCore_le
    ((QuotientGroup.eq_one_iff (x : H)).mp hq)

end CFSG.Quasithin.Chapter14.Section02
