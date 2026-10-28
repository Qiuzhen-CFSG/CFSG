module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.QuotientModel
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.SeedFusion
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Every original point-centralizer cubic has the same S5 quotient

The paired construction supplies one marked cubic. Original seed fusion
moves its marked point to the specified point, and cubic fusion inside
that full point centralizer moves the cubic itself. Conjugation transports
the full centralizer and its intrinsic odd core. The resulting order360
therefore concerns the full original centralizer of the specified cubic.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Every specified original point-centralizer cubic has literal odd-core
quotient S5, without endpoint data among the hypotheses. -/
theorem TypeAt.cubic_centralizer_quotient_model (h : TypeAt z V)
    (t : G) (ht : t∈involutionCentralizer z) (ht3 : orderOf t=3) :
    Nonempty (((centralizer ({t} : Set G)) ⧸
      pPrimeCore 2 (centralizer ({t} : Set G))) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨A,hAE,d,s,u,c,_,_,_,huz,huT,_,_,_,_,hs,hs3,huE,_⟩ :=
    h.exists_marked_cubic_quotient_six
  let := hAE
  have hsu : s∈involutionCentralizer u :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp huE.2).symm
  obtain ⟨e0⟩ := huT.cubic_centralizer_quotient_perm_five d s hsu hs hs3 huE.1
  obtain ⟨g,hgu⟩ := isConj_iff.mp huz
  let a := MulAut.conj g
  have ha : a u=z := hgu
  have has : a s∈involutionCentralizer z := by
    apply mem_centralizer_singleton_iff.mpr
    rw [←ha]
    exact (show Commute s u from mem_centralizer_singleton_iff.mp hsu).map a.toMonoidHom
  let sH : involutionCentralizer z := ⟨a s,has⟩
  let tH : involutionCentralizer z := ⟨t,ht⟩
  obtain ⟨k,hk⟩ := isConj_iff.mp (h.cubic_point_isConj sH tH
    ((orderOf_coe sH).symm.trans ((a.orderOf_eq s).trans hs3))
    ((orderOf_coe tH).symm.trans ht3))
  let e := a.trans (MulAut.conj (k:G))
  have hes : e s=t := congrArg Subtype.val hk
  let eC : centralizer ({s} : Set G) ≃* centralizer ({t} : Set G) :=
    (CentralizerSmallKernelTransport.centralizerEquiv e s).trans
      (MulEquiv.subgroupCongr (congrArg (fun x:G => centralizer ({x}:Set G)) hes))
  let eQ := QuotientGroup.congr (pPrimeCore 2 (centralizer ({s}:Set G)))
    (pPrimeCore 2 (centralizer ({t}:Set G))) eC (pPrimeCore_map_iso 2 eC)
  exact ⟨eQ.symm.trans e0⟩

/-- The full original centralizer of every point-centralizer cubic has
order360. Its odd core is the original cubic subgroup of order3. -/
theorem TypeAt.cubic_centralizer_card (h : TypeAt z V)
    (t : G) (ht : t∈involutionCentralizer z) (ht3 : orderOf t=3) :
    Nat.card (centralizer ({t} : Set G))=360 := by
  let C := centralizer ({t}:Set G)
  let O := pPrimeCore 2 C
  obtain ⟨e⟩ := h.cubic_centralizer_quotient_model t ht ht3
  have hO3 : Nat.card O=3 := by
    rw [←card_map_of_injective C.subtype_injective,
      h.cubic_centralizer_oddCore t ht ht3,Nat.card_zpowers,ht3]
  have hX : Nat.card (C⧸O)=120 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [card_eq_card_quotient_mul_card_subgroup O,hO3,hX]

end CFSG.Quasithin.HigmanSims
