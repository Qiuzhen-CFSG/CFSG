module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.MarkedSix
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.QuotientThreeDivisibility
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.NonseedInvolution
public import Theory.GroupTheory.Recognition.DihedralEightCentralizer.Classification
public import Theory.GroupTheory.Recognition.DihedralEightCentralizer.OddKernelFusion

/-!
# The actual cubic-centralizer quotient is S5

The original marked involution retains its full dihedral Sylow centralizer
in the odd-core quotient. The original full sixteen-normalizer supplies a
marked S3, excluding S4. An actual opposite reflection lies outside the
original involution class, excluding the two simple quotient models by
coprime involution fusion through the original cubic kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The literal odd-core quotient of the specified original cubic
centralizer is S5. All endpoint and point markings remain original. -/
theorem TypeAt.cubic_centralizer_quotient_perm_five (h : TypeAt z V)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (t : G) (htz : t∈involutionCentralizer z) (ht : t∈d.carrier) (ht3 : orderOf t=3)
    (hzN : z∈normalizer (A : Set G)) :
    Nonempty (((centralizer ({t} : Set G)) ⧸
      pPrimeCore 2 (centralizer ({t} : Set G))) ≃* Equiv.Perm (Fin 5)) := by
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let X := C⧸O
  let q := QuotientGroup.mk' O
  obtain ⟨zC,hz,hz2,hObot,hO,_,_,_,S,_,⟨eS⟩,hS,e,_⟩ :=
    h.cubic_centralizer_oddCore_quotient t htz ht3
  let T : Sylow 2 X := S.mapSurjective (f:=q) (QuotientGroup.mk'_surjective O)
  have hthree := h.cubic_centralizer_quotient_three_dvd d t htz ht ht3
  have hnot4 := (h.cubic_quotient_marked_six d t htz ht ht3 hzN).choose_spec.2.2.2.2.2.2
  have hmodels := DihedralEightCentralizer.model_alternative T (e.symm.trans eS)
    (q zC) hz2 hS.symm hObot hthree
  rcases hmodels with hfour | hfive | hseven | hsix
  · exact False.elim (hnot4 hfour)
  · exact hfive
  all_goals
    have hk3 : Nat.card q.ker=3 := by
      rw [QuotientGroup.ker_mk',←card_map_of_injective C.subtype_injective,hO,
        Nat.card_zpowers,ht3]
    obtain ⟨x,hx2,hxt,hxz⟩ := h.exists_nonseed_cubic_involution t htz ht3
    let xC : C := ⟨x,mem_centralizer_singleton_iff.mpr hxt.eq⟩
    have hxC2 : orderOf xC=2 := (orderOf_coe xC).symm.trans hx2
    have hzC2 : orderOf zC=2 := (orderOf_coe zC).symm.trans (hz ▸ h.involution)
    apply False.elim
    apply hxz
    have hh : IsConj xC zC :=
      DihedralEightCentralizer.involutions_isConj_of_cubic_kernel_seven_or_six
        q (QuotientGroup.mk'_surjective O) hk3 (by first | exact Or.inl hseven | exact Or.inr hsix)
        hxC2 hzC2
    have hG := C.subtype.map_isConj hh
    change IsConj x (zC : G) at hG
    rwa [hz] at hG

end CFSG.Quasithin.HigmanSims
