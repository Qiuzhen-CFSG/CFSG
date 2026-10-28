module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.UniversalModel
public import Theory.GroupTheory.CentralCubicSymmetricFive

/-!
# The full original cubic centralizer splits as C3 times S5

The actual odd core is the literal cubic subgroup. It is central in the
full cubic centralizer. The prescribed quotient is S5, and the central
cubic extension theorem supplies a section of that same map. The product
equivalence retains multiplication by the original <t>, and the quotient
of each product is exactly its second coordinate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The full centralizer of the specified original cubic is the direct
product of its literal cyclic cubic and an actual section of its S5
quotient. Both multiplication and the quotient coordinates are retained. -/
theorem TypeAt.cubic_centralizer_split (h : TypeAt z V) (t : G)
    (ht : t∈involutionCentralizer z) (ht3 : orderOf t=3) :
    let C := centralizer ({t} : Set G)
    let O := pPrimeCore 2 C
    let q := QuotientGroup.mk' O
    ∃ φ : (C⧸O) ≃* Equiv.Perm (Fin 5),
      ∃ s : Equiv.Perm (Fin 5) →* C,
        (φ.toMonoidHom.comp q).comp s=MonoidHom.id (Equiv.Perm (Fin 5)) ∧
        O.map C.subtype=zpowers t ∧
        ∃ e : (zpowers t × Equiv.Perm (Fin 5)) ≃* C,
          (∀ k g, (e (k,g) : G)=(k : G)*(s g : G)) ∧
          (∀ k g, φ (q (e (k,g)))=g) ∧
          Nonempty (C ≃* (Multiplicative (ZMod 3) × Equiv.Perm (Fin 5))) := by
  let C := centralizer ({t} : Set G)
  let O := pPrimeCore 2 C
  let q := QuotientGroup.mk' O
  obtain ⟨φ⟩ := h.cubic_centralizer_quotient_model t ht ht3
  let f := φ.toMonoidHom.comp q
  have hf : Function.Surjective f := φ.surjective.comp (QuotientGroup.mk'_surjective O)
  have hk : f.ker=O := by
    ext x
    change φ (q x)=1 ↔ x∈O
    rw [φ.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hO : O.map C.subtype=zpowers t := h.cubic_centralizer_oddCore t ht ht3
  have hkmap : f.ker.map C.subtype=zpowers t := hk ▸ hO
  have hk3 : Nat.card f.ker=3 := by
    rw [←card_map_of_injective C.subtype_injective,hkmap,Nat.card_zpowers,ht3]
  have hkc : f.ker≤center C := by
    intro x hx
    have hxt : (x : G)∈zpowers t := hkmap ▸ mem_map_of_mem C.subtype hx
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hxt
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y : G)*(x : G)=(x : G)*(y : G)
    rw [←hn]
    exact (show Commute (y : G) t from mem_centralizer_singleton_iff.mp y.property).zpow_right n
  obtain ⟨s,hs,e0,he0⟩ := CentralExtension.exists_marked_section_of_cubic_kernel f hf hkc hk3
  let k : f.ker ≃* zpowers t :=
    (f.ker.equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hkmap)
  have hkval (a : f.ker) : (k a : G)=((a : C) : G) := rfl
  let e := (MulEquiv.prodCongr k.symm (MulEquiv.refl (Equiv.Perm (Fin 5)))).trans e0
  have he (a : zpowers t) (g : Equiv.Perm (Fin 5)) :
      (e (a,g) : G)=(a : G)*(s g : G) := by
    change (e0 (k.symm a,g) : G)=_
    rw [he0]
    change (((k.symm a : f.ker) : C) : G)*(s g : G)=(a : G)*(s g : G)
    exact congrArg (fun x : G => x*(s g : G))
      ((hkval (k.symm a)).symm.trans (congrArg Subtype.val (k.apply_symm_apply a)))
  have heq (a : zpowers t) (g : Equiv.Perm (Fin 5)) : φ (q (e (a,g)))=g := by
    change f (e0 (k.symm a,g))=g
    rw [he0,map_mul,show f ((k.symm a : f.ker) : C)=1 from (k.symm a).property,one_mul]
    exact DFunLike.congr_fun hs g
  let l : zpowers t ≃* Multiplicative (ZMod 3) := mulEquivOfCyclicCardEq (by
    rw [Nat.card_zpowers,ht3]
    simp)
  exact ⟨φ,s,hs,hO,e,he,heq,⟨e.symm.trans (MulEquiv.prodCongr l (MulEquiv.refl _))⟩⟩

end CFSG.Quasithin.HigmanSims
