module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCommutators
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.LongCentralization

/-!
# Exclusion of the prepared degree-two unitary comparison

For any original outer involution f, four actual images of C_T(f)∩L in
L/O₂(L) give two inner actors and two vectors fixed by f. Simultaneous
quotient/module alignment makes the sum of their displacements nonzero,
singular and fixed by the actors. The literal action convention transports
it to a product of commutators in the FULL C_T(f). The existing singular
detector places this product in the ORIGINAL right-residual center.

For the SAME maximizing degree-two involution already selected, the checked
quotient bound supplies at least q≥4 actors, whereas the escaping ambient
two-normalizer forces the derived subgroup to avoid that center. This is the
contradiction. Both orientations, q=4 and every ambient input are retained;
no identification with a marked graph centralizer is assumed.

The ordinary-even branch still requires its own centralizer comparison.
Source: Aschbacher–Smith F.4.35,37–38, pp.292–294, refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

/-- Four inner quotient actors in the full fixed Sylow force a nontrivial
commutator in the original long-root group. -/
theorem Preparation.unitaryFour_outer_long_commutator
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hlarge : 4 ≤ (L.pCoreIn 2).relIndex
      (((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G))) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    (_root_.commutator P).map P.subtype ⊓
      (center (residual H)).map (residual H).subtype ≠ ⊥ := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨e,f,hf⟩ := d.unitary_core_hermitian_model h hH hp m hm hc
  let Q := L.pCoreIn 2
  let a : normalizer (L : Set G) := ⟨u.val,h.sylow_normalizes u.property⟩
  let c := L.normalizerMonoidHom a
  have hN : normalizer (L : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  let b := Q.normalizerMonoidHom (inclusion hN a)
  let k := f.symm.trans (b.trans f)
  let E : Space m ≃+ Space m :=
    { toFun x := (k (Multiplicative.ofAdd x)).toAdd
      invFun x := (k.symm (Multiplicative.ofAdd x)).toAdd
      left_inv x := congrArg Multiplicative.toAdd (k.symm_apply_apply (Multiplicative.ofAdd x))
      right_inv x := congrArg Multiplicative.toAdd (k.apply_symm_apply (Multiplicative.ofAdd x))
      map_add' x y := congrArg Multiplicative.toAdd (k.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) }
  let φ := (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)
  let α := φ a
  have ha2 : a^2=1 := Subtype.ext (by
    have hh := congrArg (fun t : T => t.val) (pow_orderOf_eq_one u)
    rwa [hu] at hh)
  have hα : α^2=1 := by change (φ a)^2=1; rw [←map_pow,ha2,map_one]
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let coord : Space m → G := fun x => (f.symm (Multiplicative.ofAdd x)).val
  have hcoord : Function.Injective coord :=
    Q.subtype_injective.comp (f.symm.injective.comp Multiplicative.ofAdd.injective)
  have hcoordf (x : Q) : coord (f x).toAdd=x.val :=
    congrArg Subtype.val (f.symm_apply_apply x)
  have hcoordE (x : Space m) : coord (E x)=u.val*coord x*u.val⁻¹ := by
    change (f.symm (f (b (f.symm (Multiplicative.ofAdd x))))).val = _
    rw [f.symm_apply_apply]
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  have hcoordAct (l : L) (x : Space m) :
      coord (action m (q l) x)=l.val*coord x*l.val⁻¹ := by
    have hh := hf l (f.symm (Multiplicative.ofAdd x))
    rw [f.apply_symm_apply] at hh
    exact hh
  have hαq (l : L) : α (q l)=q (c l) := by
    change e ((quotientAut (pCore 2 L) c)
      (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hinter (g : Matrix.SpecialLinearGroup (Fin 2) (Field m)) (x : Space m) :
      E (action m g x)=action m (α g) (E x) := by
    obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    change E (action m (q l) x)=action m (α (q l)) (E x)
    apply hcoord
    rw [hcoordE,hcoordAct,hαq,hcoordAct,hcoordE]
    have hcval : (c l).val=u.val*l.val*u.val⁻¹ :=
      normalizerMonoidHom_apply_apply_coe _ _ _
    rw [hcval]
    group
  have houter : ¬ ∃ g, α=MulAut.conj g := by
    rintro ⟨g,hg⟩
    apply ho
    let e' := e.trans (Theory.PSL2.sl2QuotientEquiv (Field m))
    have hker := d.unitaryFour_sylow_field_kernel h hH hp m hm hc e'
    change u ∈ L.subgroupOf (T : Subgroup G)
    rw [←hker]
    change Theory.PSL2.fieldProjection (Field m)
      ((MulAut.congr (Theory.PSL2.sl2QuotientEquiv (Field m))) α)=1
    rw [hg,MulAut.congr_conj]
    apply MonoidHom.mem_ker.mp
    rw [Theory.PSL2.fieldProjection_ker]
    exact ⟨_,rfl⟩
  have hE2 : Function.Involutive E := by
    intro x
    apply hcoord
    rw [hcoordE,hcoordE]
    have hu2 : u.val*u.val=1 := by
      have hh : u^2=1 := (congrArg (fun k : ℕ => u^k) hu).symm.trans (pow_orderOf_eq_one u)
      have hh' : u.val^2=1 := congrArg (fun t : T => t.val) hh
      simpa only [pow_two] using hh'
    calc
      _ = (u.val*u.val)*coord x*(u.val*u.val)⁻¹ := by group
      _ = coord x := by rw [hu2,inv_one,one_mul,mul_one]
  let I := ((T : Subgroup G) ⊓ L) ⊓ centralizer ({u.val} : Set G)
  let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
  change (_root_.commutator P).map P.subtype ⊓
    (center (residual H)).map (residual H).subtype ≠ ⊥
  have hIL : I ≤ L := inf_le_left.trans inf_le_right
  let j := q.comp (inclusion hIL)
  let B := j.range
  have hker : j.ker=Q.subgroupOf I := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) (inclusion hIL x))=1 ↔ x.val ∈ Q
    rw [←e.map_one,e.injective.eq_iff]
    exact (QuotientGroup.eq_one_iff (N := pCore 2 L) _).trans
      (mem_map_iff_mem L.subtype_injective).symm
  have hcard : 4 ≤ Nat.card B := by
    rw [←index_ker j,hker]
    exact hlarge
  have hB : IsPGroup 2 B := (T.isPGroup'.to_le
    (show I ≤ (T : Subgroup G) from inf_le_left.trans inf_le_left)).of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hBfix (g : B) : α g.val=g.val := by
    obtain ⟨l,hl⟩ := g.property
    rw [←hl]
    change α (q (inclusion hIL l))=q (inclusion hIL l)
    rw [hαq]
    congr 1
    apply Subtype.ext
    change u.val*l.val*u.val⁻¹=l.val
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp l.property.2).symm
  obtain ⟨v,w,hv,hw,X₁,X₂,hX₁,hX₂,hY,hYs,hYfix⟩ :=
    Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourCommutators.outer_fixed_displacements
      m α hα houter E hE2 hinter B hB hBfix hcard
  obtain ⟨v₀,hv₀⟩ := v.property
  obtain ⟨w₀,hw₀⟩ := w.property
  let Y := (action m v.val X₁-X₁)+(action m w.val X₂-X₂)
  have hQT : Q ≤ (T : Subgroup G) := by
    change L.pCoreIn 2 ≤ (T : Subgroup G)
    rw [←d.unitary_thompson h hH hp m hm hc]
    exact sSup_le fun _ hF => hF.1
  have hcoord_add (x y : Space m) : coord (x+y)=coord x*coord y := by
    change (f.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y)).val=_
    rw [map_mul]
    rfl
  have hcoord_sub (x y : Space m) : coord (x-y)=coord x*(coord y)⁻¹ := by
    rw [sub_eq_add_neg,hcoord_add]
    dsimp only [coord]
    rw [ofAdd_neg,map_inv]
    rfl
  have hcoordP (x : Space m) (hx : E x=x) : coord x ∈ P := by
    refine ⟨hQT (f.symm (Multiplicative.ofAdd x)).property,?_⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := hcoordE x
    rw [hx] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  have hcomm (l : I) (x : Space m) (hx : E x=x) :
      coord (action m (j l) x-x) ∈ (_root_.commutator P).map P.subtype := by
    let lP : P := ⟨l.val,l.property.1.1,l.property.2⟩
    let xP : P := ⟨coord x,hcoordP x hx⟩
    refine ⟨⁅lP,xP⁆,commutator_mem_commutator (mem_top lP) (mem_top xP),?_⟩
    rw [hcoord_sub]
    change l.val*coord x*l.val⁻¹*(coord x)⁻¹=
      coord (action m (q (inclusion hIL l)) x)*(coord x)⁻¹
    rw [hcoordAct]
    rfl
  have hyD : coord Y ∈ (_root_.commutator P).map P.subtype := by
    rw [hcoord_add]
    apply mul_mem
    · rw [←hv₀]
      exact hcomm v₀ X₁ hX₁
    · rw [←hw₀]
      exact hcomm w₀ X₂ hX₂
  have hvQ : v₀.val ∉ Q := by
    intro hh
    apply hv
    rw [←hv₀]
    change e (QuotientGroup.mk' (pCore 2 L) (inclusion hIL v₀))=1
    rw [show QuotientGroup.mk' (pCore 2 L) (inclusion hIL v₀)=1 from
      (QuotientGroup.eq_one_iff (N := pCore 2 L) _).mpr
        ((mem_map_iff_mem L.subtype_injective).mp hh),map_one]
  have hcommY : Commute v₀.val (coord Y) := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      _ = coord (action m (j v₀) Y) := (hcoordAct (inclusion hIL v₀) Y).symm
      _ = coord Y := by
        rw [hv₀]
        exact congrArg coord (hYfix v)
  have hyR : coord Y ∈ (center (residual H)).map (residual H).subtype := by
    apply (d.unitaryFour_singular_iff_right_center h hH hp m hm hc e f hf
      v₀.val v₀.property.1 hvQ (f.symm (Multiplicative.ofAdd Y)) hcommY).mp
    rw [f.apply_symm_apply]
    exact hYs
  intro hz
  have hmem : coord Y ∈ (_root_.commutator P).map P.subtype ⊓
      (center (residual H)).map (residual H).subtype := ⟨hyD,hyR⟩
  rw [hz,mem_bot] at hmem
  apply hY
  apply hcoord
  exact hmem.trans (by change 1=(f.symm 1).val; rw [map_one]; rfl)

omit hc in
/-- The prepared degree-two unitary comparison is impossible, in either
orientation and including q=4. -/
theorem Preparation.unitaryFour_degreeTwo_impossible
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    False := by
  obtain ⟨u,_,hu,ho,_,_,V,_,_,_,_,_,_,_,_,_,_,hzero,_,_,_,hsize⟩ :=
    d.unitaryFour_degreeTwo_selected_long_centralization h hH hp m hm he
  have hstrict := (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm he).1
  have hfour : 4 ≤ 2^m := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^m := Nat.pow_le_pow_right (by decide) (by omega)
  exact d.unitaryFour_outer_long_commutator h hH hp m hm (.inr he) u hu ho
    (hfour.trans hsize) hzero

/-- The original prepared unitary row has an ordinary comparison; the
extra involution in a degree-two comparison cannot occur in the ambient group. -/
theorem Preparation.unitaryFour_comparison_ordinary :
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse) :=
  hc.resolve_right (d.unitaryFour_degreeTwo_impossible h hH hp m hm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
