module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaStructure.Sylow
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.SL2NaturalFixedLifting
public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.GroupTheory.TwoQuadraticConjugateGenerators

/-!
# Campbell's fixed subgroup and Sylow commutator

The actual natural projection has kernel C_moved(H), by the known quotient
order and absence of natural invariant vectors. Fixed-vector lifting through
this central kernel identifies every relative centralizer with the inverse
image of the corresponding natural fixed space, including nonsplit modules.
The natural Sylow action is quadratic, so the lifted Sylow action is too.
Two actual conjugate Sylow subgroups generate H. Since moved=[moved,H],
the two-quadratic-generation theorem identifies C_moved(S)=[S,moved].
The final consumer gives [A,F]=[J(S),F]=C_V(S) on the literal source marking.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.1 and II.4.3–4.5,
printed pp.21–26, from Aschbacher–Smith C.1.17 and Baumann-fixedness.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
 {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
private theorem natural_fixed_zero (v : Fin 2 → F)
    (hv : ∀ g : SL(2,F), Matrix.mulVec g.val v = v) : v = 0 := by
  by_contra hn
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq F v ![1,0] hn (by intro he; simpa using congrFun he 0)
  obtain ⟨b,hb⟩ := Matrix.SL2.exists_mulVec_eq F v ![0,1] hn (by intro he; simpa using congrFun he 1)
  have he := ha.symm.trans ((hv a).trans ((hv b).symm.trans hb))
  have he0 := congrFun he 0
  simp at he0

theorem InLocalClass.natural_projection_kernel (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (q : H →* SL(2,F)) (hq : Function.Surjective q)
    (f : moved e →* Multiplicative (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g w, (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd) :
    f.ker = (center H).subgroupOf (moved e) := by
  have hc : (center H).subgroupOf (moved e) ≤ f.ker := by
    intro w hw
    apply Multiplicative.toAdd.injective
    apply natural_fixed_zero
    intro a
    obtain ⟨g,rfl⟩ := hq a
    rw [←he]
    have hc : movedConjugate e g w = w := by
      apply Subtype.ext
      change g*(w:H)*g⁻¹=w
      have hh : g*(w:H)=(w:H)*g := mem_center_iff.mp hw g
      rw [hh,mul_inv_cancel_right]
    rw [hc]
  apply le_antisymm ?_ hc
  by_contra hn
  have hi := index_strictAnti (lt_of_le_not_ge hc hn)
  have hker : f.ker.index = Nat.card F^2 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top]
    change Nat.card (Fin 2 → F) = Nat.card F^2
    simp only [Nat.card_fun,Nat.card_fin]
  have hC : ((center H).subgroupOf (moved e)).index = Nat.card F^2 := by
    rw [←h.movedFixed_eq_center hB m]
    exact m.module_card e
  rw [hker,hC] at hi
  exact hi.false

theorem InLocalClass.natural_projection_fixed_lift (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (q : H →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = localKernel e)
    (f : moved e →* Multiplicative (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g w, (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd)
    (g : H) (w : moved e) (hfix : f (movedConjugate e g w) = f w) :
    movedConjugate e g w = w := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨_,_,_,_,_,_,_,hC⟩ := h.exists_faithful_natural_action m
  have hk' : q.ker = centralizer (moved e : Set H) := hk.trans hC.symm
  let ρ := NormalElementaryQuotient.representation (moved e) q hq hk'
  let p := f.toAdditiveLeft.toZModLinearMap 2
  have ha (a : H) (v : moved e) : ρ (q a) (Additive.ofMul v) =
      Additive.ofMul (movedConjugate e a v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply (moved e) q hq hk' a (Additive.ofMul v)
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨w,hw⟩ := hf (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w,congrArg Multiplicative.toAdd hw⟩
  have he' (a : SL(2,F)) (v : Additive (moved e)) : p (ρ a v) = a • p v := by
    obtain ⟨g,rfl⟩ := hq a
    rw [show v = Additive.ofMul v.toMul from rfl,ha]
    exact he g v.toMul
  have hk'' (v : Additive (moved e)) (hv : p v = 0) (a : SL(2,F)) : ρ a v = v := by
    obtain ⟨g,rfl⟩ := hq a
    rw [show v = Additive.ofMul v.toMul from rfl,ha]
    have hfv : v.toMul ∈ f.ker := by
      apply Multiplicative.toAdd.injective
      exact hv
    have hcv : (v.toMul : H) ∈ center H := by
      have hh := (InLocalClass.natural_projection_kernel h hB m q hq f hf he) ▸ hfv
      exact hh
    apply Additive.toMul.injective
    apply Subtype.ext
    change g*(v.toMul:H)*g⁻¹=v.toMul
    rw [mem_center_iff.mp hcv g,mul_inv_cancel_right]
  have hh := SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel ρ p.toAddMonoidHom hp he' hk''
    (q g) (Additive.ofMul w) (by rw [ha]; exact congrArg Multiplicative.toAdd hfix)
  rw [ha] at hh
  exact Additive.ofMul.injective hh

theorem InLocalClass.centralizer_moved_eq_natural_fixed_preimage (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (q : H →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = localKernel e)
    (f : moved e →* Multiplicative (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g w, (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd)
    (A : Subgroup H) :
    (centralizer (A : Set H)).subgroupOf (moved e) =
      (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed (A.map q)).comap f := by
  ext w
  constructor
  · intro hw a ha
    obtain ⟨g,hg,rfl⟩ := ha
    have hwg : movedConjugate e g w = w := by
      apply Subtype.ext
      change g*(w:H)*g⁻¹=w
      have hh : g*(w:H)=(w:H)*g := hw g hg
      rw [hh,mul_inv_cancel_right]
    exact (he g w).symm.trans (congrArg (fun w => (f w).toAdd) hwg)
  · intro hw g hg
    have hh := InLocalClass.natural_projection_fixed_lift h hB m q hq hk f hf he g w
      (Multiplicative.toAdd.injective ((he g w).trans (hw (q g) (mem_map_of_mem q hg))))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)

theorem InLocalClass.exists_campbell_fixed_projection (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) :
    ∃ (q : H →* SL(2,F)) (f : moved e →* Multiplicative (Fin 2 → F)),
      Function.Surjective q ∧ q.ker = localKernel e ∧ Function.Surjective f ∧
      f.ker = (center H).subgroupOf (moved e) ∧
      (∀ g w, (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd) ∧
      ∀ A : Subgroup H, (centralizer (A : Set H)).subgroupOf (moved e) =
        (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed (A.map q)).comap f := by
  obtain ⟨q,f,hq,hk,hf,he⟩ := h.exists_campbell_projection hB m
  exact ⟨q,f,hq,hk,hf,InLocalClass.natural_projection_kernel h hB m q hq f hf he,he,
    InLocalClass.centralizer_moved_eq_natural_fixed_preimage h hB m q hq hk f hf he⟩

omit [CharP F 2] in
private theorem sylow_quadratic [Algebra (ZMod 2) F] (P : Sylow 2 SL(2,F)) :
    Representation.BinaryOffender.IsQuadratic
      (Representation.SL2NaturalOffenders.NoStrong.natural (F := F)) (P : Subgroup SL(2,F)) := by
  let L : Subgroup SL(2,F) := ⊤
  let a : L ≃* SL(2,F) := Subgroup.topEquiv
  let R := P.mapSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  have hm : (R : Subgroup L).map L.subtype = (P : Subgroup SL(2,F)) := by
    change ((P : Subgroup SL(2,F)).map a.symm.toMonoidHom).map L.subtype = _
    rw [map_map]
    have hi : L.subtype.comp a.symm.toMonoidHom = MonoidHom.id _ := rfl
    rw [hi,map_id]
  have hh := Representation.SL2NaturalOffenders.Ratios.sylowImage_quadratic L a
    (Representation.SL2NaturalOffenders.NoStrong.natural (F := F)) (fun _ _ => rfl) R
  rwa [hm] at hh

theorem InLocalClass.sylow_commutator_moved_centralizes (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (S : Sylow 2 H) :
    ⁅(S : Subgroup H),moved e⁆ ≤ centralizer (S : Set H) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨q,f,hq,hk,hf,he⟩ := h.exists_campbell_projection hB m
  have hquad := sylow_quadratic (S.mapSurjective hq)
  apply commutator_le.mpr
  intro a ha v hv b hb
  let w : moved e := ⟨⁅a,v⁆,commutator_le_right (S : Subgroup H) (moved e)
    (commutator_mem_commutator ha hv)⟩
  have hfw : (f w).toAdd = Matrix.mulVec (q a).val (f ⟨v,hv⟩).toAdd - (f ⟨v,hv⟩).toAdd := by
    have hew : w = movedConjugate e a ⟨v,hv⟩ * (⟨v,hv⟩ : moved e)⁻¹ := by
      apply Subtype.ext
      change ⁅a,v⁆ = (a*v*a⁻¹)*v⁻¹
      rfl
    rw [hew,map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg,he]
  have hfix : f (movedConjugate e b w) = f w := by
    apply Multiplicative.toAdd.injective
    rw [he,hfw]
    exact hquad (q b) (mem_map_of_mem q hb) (q a) (mem_map_of_mem q ha) (f ⟨v,hv⟩).toAdd
  have hh := InLocalClass.natural_projection_fixed_lift h hB m q hq hk f hf he b w hfix
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)

variable {J : Type*} [Group J]
theorem InLocalClass.exists_two_sylow_generators (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) :
    ∃ g ∈ pResidual 2 H, (d.sylow : Subgroup H) ⊔
      (d.sylow : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ := by
  obtain ⟨A,g,hA,hg,hgen,_⟩ := h.exists_two_maxElementary_generators hB m d hS
  refine ⟨g,hg,top_unique ?_⟩
  rw [←hgen]
  apply sup_le
  · exact (sup_le (pCore_isPGroup.le_sylow_of_normal d.sylow) hA.1).trans le_sup_left
  · exact (map_mono hA.1).trans le_sup_right

theorem InLocalClass.sylow_fixed_eq_commutator (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) :
    moved e ⊓ centralizer (d.sylow : Set H) = ⁅(d.sylow : Subgroup H),moved e⁆ := by
  let : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨g,_,hgen⟩ := InLocalClass.exists_two_sylow_generators h hB m d hS
  exact fixed_eq_commutator_of_two_quadratic_conjugates (moved e) (d.sylow : Subgroup H) g hgen
    (h.moved_commutator_eq_self hB m) (InLocalClass.sylow_commutator_moved_centralizes h hB m d.sylow)
    (InLocalClass.sylow_commutator_moved_centralizes h hB m
      (d.sylow.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective))

theorem InLocalClass.campbell_fixed_commutator_identities (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H)) (hAQ : ¬ A ≤ pCore 2 H) :
    ⁅A,Campbell.F H⁆ = Campbell.V H ⊓ centralizer (d.sylow : Set H) ∧
      ⁅Campbell.J (d.sylow : Subgroup H),Campbell.F H⁆ =
        Campbell.V H ⊓ centralizer (d.sylow : Set H) := by
  have he := h.campbell_commutator_identities hB m d A hA hAQ
  have hz : ⁅(d.sylow : Subgroup H),Campbell.V H⁆ =
      Campbell.V H ⊓ centralizer (d.sylow : Set H) := by
    rw [h.campbellV_eq_moved hB m]
    exact (InLocalClass.sylow_fixed_eq_commutator h hB m d hS).symm
  exact ⟨he.1.trans hz,he.2.trans hz⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
