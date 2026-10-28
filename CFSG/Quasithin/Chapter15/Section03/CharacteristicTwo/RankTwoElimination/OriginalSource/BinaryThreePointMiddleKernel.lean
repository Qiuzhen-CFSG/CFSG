module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSynchronizedSections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalCoreQuotient
public import Theory.Representation.PSL3Two.NaturalDualCentralizer

/-!
# The original middle core lies in the original point kernel

The literal quotient Q/C_Q(W) is equivariantly the original natural seed.
The synchronized marking makes D/Phi doubled dual for that same actor.
Its map to the natural seed therefore vanishes. Since Phi already lies in
N, this proves D lies in N, retaining the original quotient denominator.

Source context: Aschbacher--Smith 15.3.23 and MS93 (4.5).
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G]

private theorem dual_double_natural_zero
    (T : (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual).IntertwiningMap BinaryLinearThree.W) :
    T = 0 := by
  have h₁ := BinaryLinearThree.NaturalDual.dual_natural_zero
    (T.comp (IntertwiningMap.inl (ZMod 2) BinaryLinearThree.W.dual BinaryLinearThree.W.dual))
  have h₂ := BinaryLinearThree.NaturalDual.dual_natural_zero
    (T.comp (IntertwiningMap.inr (ZMod 2) BinaryLinearThree.W.dual BinaryLinearThree.W.dual))
  ext v
  have hleft : T (v.1,0) = 0 := congrArg (fun f => f v.1) h₁
  have hright : T (0,v.2) = 0 := congrArg (fun f => f v.2) h₂
  have he : v = (v.1,0)+(0,v.2) := by simp
  rw [he,map_add,hleft,hright,add_zero]
  rfl

private theorem dual_section_natural_hom_trivial
    (L D Phi V : Subgroup G) (a : L →* Matrix.PSL3Two.SL)
    (ha : Function.Surjective a)
    (hd : HasSectionModel L D Phi a (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual))
    (hn : HasSectionModel L V ⊥ a BinaryLinearThree.W)
    (f : D →* V) (hkill : Phi.subgroupOf D ≤ f.ker)
    (hf : ∀ (l : L) (x y : D), (y:G)=l*x*(l:G)⁻¹ →
      (f y:G)=l*f x*(l:G)⁻¹) : ∀ x : D, f x = 1 := by
  obtain ⟨_,hLD,_,hPhi,ed,hed⟩ := hd
  obtain ⟨_,_,_,hbot,en,hen⟩ := hn
  let := hPhi
  let := hbot
  let pd := ed.toMonoidHom.comp (QuotientGroup.mk' (Phi.subgroupOf D))
  let pn := en.toMonoidHom.comp (QuotientGroup.mk' ((⊥:Subgroup G).subgroupOf V))
  have hpd : Function.Surjective pd := ed.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkd : pd.ker = Phi.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ ed.injective,QuotientGroup.ker_mk']
  have hkn : pn.ker = ⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ en.injective,QuotientGroup.ker_mk',bot_subgroupOf]
  have hk : pd.ker ≤ (pn.comp f).ker := by
    rw [hkd]
    intro x hx
    change pn (f x) = 1
    rw [show f x=1 from hkill hx,map_one]
  let q := pd.liftOfSurjective hpd ⟨pn.comp f,hk⟩
  have hq (x : D) : q (pd x)=pn (f x) := by simp [q]
  let ql := (AddMonoidHom.toMultiplicative.symm q).toZModLinearMap 2
  let T : (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual).IntertwiningMap BinaryLinearThree.W := {
    toLinearMap := ql
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      obtain ⟨l,rfl⟩ := ha g
      obtain ⟨x,hx⟩ := hpd (Multiplicative.ofAdd v)
      let y := D.normalizerMonoidHom (inclusion hLD l) x
      have hd := hed l x y rfl
      have hn := hen l (f x) (f y) (hf l x y rfl)
      change (pd y).toAdd = (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual) (a l)
        (pd x).toAdd at hd
      have hv : (pd x).toAdd = v := congrArg Multiplicative.toAdd hx
      change ql ((BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual) (a l) v) =
        BinaryLinearThree.W (a l) (ql v)
      rw [←hv,←hd]
      change (q (pd y)).toAdd = BinaryLinearThree.W (a l) (q (pd x)).toAdd
      rw [hq,hq]
      exact hn }
  intro x
  have hz := congrArg (fun T : (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual).IntertwiningMap
    BinaryLinearThree.W => T (pd x).toAdd) (dual_double_natural_zero T)
  have hp : pn (f x)=1 := by
    change (q (pd x)).toAdd = 0 at hz
    rw [hq] at hz
    exact hz
  have hx : f x ∈ pn.ker := hp
  rwa [hkn] at hx

variable [Finite G]

/-- The actual middle core C_Q(Phi(Q)) lies in the actual O₂(C_G(z)). -/
theorem binary_three_source_natural_middle_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    let Q := LinearThree.commutatorCore c.L
    Q ⊓ centralizer (frattiniIn Q : Set G) ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  obtain ⟨hfix,_,_,hn,E,hE⟩ := binary_three_source_natural_core_quotient
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  let := hn
  let π := QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Q)
  let f : D →* V := E.toMonoidHom.comp (π.comp (inclusion (show D ≤ Q from inf_le_left)))
  have hPhiN : Phi ≤ N := binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hk : Phi.subgroupOf D ≤ f.ker := by
    intro x hx
    change E (π (inclusion inf_le_left x))=1
    apply E.map_eq_one_iff.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    have hm : (x:G) ∈ Q ⊓ N := ⟨x.property.1,hPhiN hx⟩
    rw [←hfix] at hm
    exact hm.2
  obtain ⟨a,ha,_,hseed,_,hdual,_⟩ := binary_three_source_synchronized_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hf (l : c.L) (x y : D) (hy : (y:G)=l*x*(l:G)⁻¹) :
      (f y:G)=l*f x*(l:G)⁻¹ := hE l (inclusion inf_le_left x) (inclusion inf_le_left y) hy
  have hzero := dual_section_natural_hom_trivial c.L D Phi V a ha hdual hseed f hk hf
  change D ≤ N
  intro x hx
  have he := hzero ⟨x,hx⟩
  have heq : π (⟨x,hx.1⟩ : Q)=1 := E.map_eq_one_iff.mp he
  have hcW : x ∈ centralizer (W : Set G) :=
    (QuotientGroup.eq_one_iff (N := (centralizer (W : Set G)).subgroupOf Q) (⟨x,hx.1⟩ : Q)).mp heq
  exact (hfix.le ⟨hx.1,hcW⟩).2

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
