module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiveRowAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiKernel
public import Theory.Representation.PSL3Two.SingerPairPolynomials
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The two original point-kernel intersections in the binary-five carrier

The two coprime Singer polynomials compare the literal q(Q) action with the
original common-marked sections D/Phi and Q/D. The natural row type forces
R=D. The dual row type forces R intersect D=Phi and R join D=Q. Neither
case is selected by the geometry alone, and no unique-head assumption is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryLinearThree Matrix.PSL3Two.OuterInvolutionSinger

private def polynomialWord {G : Type*} [Group G] {L Q : Subgroup G}
    (hLQ : L ≤ normalizer Q) (l : L) (n : ℕ) (x : Q) : Q :=
  Q.normalizerMonoidHom (inclusion hLQ (l^3)) x *
    Q.normalizerMonoidHom (inclusion hLQ (l^n)) x * x

private theorem polynomialWord_map {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {L Q : Subgroup G} (hLQ : L ≤ normalizer Q)
    (a : L →* BinaryLinearThree.Group) (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (p : Q →* Multiplicative V)
    (he : ∀ (l : L) (x y : Q), y.val=l.val*x.val*l.val⁻¹ →
      (p y).toAdd=ρ (a l) (p x).toAdd)
    (l : L) (n : ℕ) (x : Q) :
    (p (polynomialWord hLQ l n x)).toAdd =
      ρ (a (l^3)) (p x).toAdd+ρ (a (l^n)) (p x).toAdd+(p x).toAdd := by
  change (p (_ * _ * x)).toAdd=_
  rw [p.map_mul,p.map_mul]
  change (p (Q.normalizerMonoidHom (inclusion hLQ (l^3)) x)).toAdd+
    (p (Q.normalizerMonoidHom (inclusion hLQ (l^n)) x)).toAdd+(p x).toAdd=_
  rw [he (l^3) x (Q.normalizerMonoidHom (inclusion hLQ (l^3)) x) rfl,
    he (l^n) x (Q.normalizerMonoidHom (inclusion hLQ (l^n)) x) rfl]

private theorem section_word_mem {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    {L D E : Subgroup G} {a : L →* BinaryLinearThree.Group}
    {ρ : Representation (ZMod 2) BinaryLinearThree.Group V}
    (hs : HasSectionModel L D E a ρ) (l : L) (n : ℕ)
    (hpoly : ∀ v, ρ (a (l^3)) v+ρ (a (l^n)) v+v=0) (x : D) :
    (polynomialWord hs.2.1 l n x).val ∈ E := by
  obtain ⟨_,hLD,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf D))
  have hp : p.ker=E.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hh := polynomialWord_map hLD a ρ p he l n x
  rw [hpoly] at hh
  have hm : polynomialWord hLD l n x ∈ p.ker := Multiplicative.toAdd.injective hh
  rw [hp] at hm
  exact hm

private theorem section_card {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    {L D E : Subgroup G} {a : L →* BinaryLinearThree.Group}
    {ρ : Representation (ZMod 2) BinaryLinearThree.Group V}
    (hs : HasSectionModel L D E a ρ) : Nat.card D=Nat.card V*Nat.card E := by
  obtain ⟨hED,_,_,hn,e,_⟩ := hs
  let := hn
  have hc := card_eq_card_quotient_mul_card_subgroup (E.subgroupOf D)
  rw [Nat.card_congr e.toEquiv,Nat.card_congr (Multiplicative.toAdd : Multiplicative V ≃ V),
    Nat.card_congr (subgroupOfEquivOfLe hED).toEquiv] at hc
  exact hc

private theorem natural_kernel_contains_middle {G : Type*} [Group G]
    {L Q D Phi R : Subgroup G} (hLQ : L ≤ normalizer Q) (hDQ : D ≤ Q)
    (a : L →* BinaryLinearThree.Group)
    (hd : HasSectionModel L D Phi a (W.dual.prod W.dual))
    (hPhiR : Phi ≤ R) (p : Q →* Multiplicative (Vector × Vector))
    (hp : p.ker=R.subgroupOf Q)
    (he : ∀ (l : L) (x y : Q), y.val=l.val*x.val*l.val⁻¹ →
      (p y).toAdd=(W.prod W) (a l) (p x).toAdd)
    (l : L) (hl : a l=singer) : D ≤ R := by
  intro x hx
  let xd : D := ⟨x,hx⟩
  let xq : Q := ⟨x,hDQ hx⟩
  have hw : (polynomialWord hLQ l 1 xq).val ∈ Phi :=
    section_word_mem hd l 1 (by
      intro v
      simpa only [map_pow,hl,pow_one] using SingerPairPolynomials.dual_pair.1 v) xd
  have hzero : p (polynomialWord hLQ l 1 xq)=1 := by
    have hh : polynomialWord hLQ l 1 xq ∈ R.subgroupOf Q := hPhiR hw
    rwa [←hp] at hh
  have hh := polynomialWord_map hLQ a (W.prod W) p he l 1 xq
  rw [hzero] at hh
  simp only [a.map_pow,hl,pow_one] at hh
  have hz : (p xq).toAdd=0 := SingerPairPolynomials.natural_pair.2.1 (by
    simpa only [toAdd_one,map_zero,add_zero] using hh.symm)
  have hxk : xq ∈ p.ker := Multiplicative.toAdd.injective hz
  rw [hp] at hxk
  exact hxk

private theorem dual_kernel_sup_middle {G : Type*} [Group G]
    {L Q D R : Subgroup G} (hLQ : L ≤ normalizer Q)
    (a : L →* BinaryLinearThree.Group)
    (ht : HasSectionModel L Q D a (W.prod W))
    (hRQ : R ≤ Q) (p : Q →* Multiplicative
      (Module.Dual (ZMod 2) Vector × Module.Dual (ZMod 2) Vector))
    (hps : Function.Surjective p) (hp : p.ker=R.subgroupOf Q)
    (he : ∀ (l : L) (x y : Q), y.val=l.val*x.val*l.val⁻¹ →
      (p y).toAdd=(W.dual.prod W.dual) (a l) (p x).toAdd)
    (l : L) (hl : a l=singer) : R ⊔ D=Q := by
  apply le_antisymm (sup_le hRQ ht.1)
  intro x hx
  let xq : Q := ⟨x,hx⟩
  obtain ⟨v,hv⟩ := SingerPairPolynomials.dual_pair.2.2 (p xq).toAdd
  obtain ⟨y,hy⟩ := hps (Multiplicative.ofAdd v)
  let w := polynomialWord hLQ l 2 y
  have hw : w.val ∈ D := section_word_mem ht l 2 (by
    intro z
    simpa only [map_pow,hl] using SingerPairPolynomials.natural_pair.1 z) y
  have heq : p w=p xq := by
    apply Multiplicative.toAdd.injective
    have hh := polynomialWord_map hLQ a (W.dual.prod W.dual) p he l 2 y
    simp only [a.map_pow,hl,hy] at hh
    exact hh.trans hv
  have hdiff : xq/w ∈ R.subgroupOf Q := by
    rw [←hp]
    change p (xq/w)=1
    rw [p.map_div,heq]
    exact div_self' _
  have hmem : (xq : G)/(w : G)*(w : G) ∈ R ⊔ D :=
    (R ⊔ D).mul_mem (mem_sup_left hdiff) (mem_sup_right hw)
  simpa only [div_mul_cancel] using hmem

private theorem image_coordinates {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (C L Q : Subgroup G) (hLC : L ≤ C) (hQC : Q ≤ C)
    (a : L →* BinaryLinearThree.Group) (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (j : ((Q.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))) ≃* Multiplicative V)
    (he : ∀ (l : L) (x y : (Q.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))),
      y.val=(QuotientGroup.mk' (pCore 2 C) (inclusion hLC l))*x.val*
        (QuotientGroup.mk' (pCore 2 C) (inclusion hLC l))⁻¹ →
      (j y).toAdd=ρ (a l) (j x).toAdd) :
    ∃ p : Q →* Multiplicative V, Function.Surjective p ∧
      p.ker=(Q ⊓ C.pCoreIn 2).subgroupOf Q ∧
      ∀ (l : L) (x y : Q), y.val=l.val*x.val*l.val⁻¹ →
        (p y).toAdd=ρ (a l) (p x).toAdd := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let r := (q.subgroupMap (Q.subgroupOf C)).comp (subgroupOfEquivOfLe hQC).symm.toMonoidHom
  let p := j.toMonoidHom.comp r
  refine ⟨p,j.surjective.comp ((q.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hQC).symm.surjective),?_,?_⟩
  · ext x
    change j (r x)=1 ↔ x.val ∈ Q ⊓ C.pCoreIn 2
    rw [j.map_eq_one_iff]
    constructor
    · intro hx
      have hqx : q ⟨x.val,hQC x.property⟩=1 := congrArg Subtype.val hx
      have hm : (⟨x.val,hQC x.property⟩ : C) ∈ pCore 2 C := (QuotientGroup.eq_one_iff _).mp hqx
      exact ⟨x.property,mem_map_of_mem C.subtype hm⟩
    · rintro ⟨_,hx⟩
      obtain ⟨y,hy,hyx⟩ := hx
      have hy' : y=(⟨x.val,hQC x.property⟩ : C) := Subtype.ext hyx
      have hm : (⟨x.val,hQC x.property⟩ : C) ∈ pCore 2 C := hy' ▸ hy
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr hm
  · intro l x y hy
    apply he l (r x) (r y)
    change q ⟨y.val,hQC y.property⟩=q (inclusion hLC l)*q ⟨x.val,hQC x.property⟩*(q (inclusion hLC l))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    exact congrArg q (Subtype.ext hy)

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine original binary-five source has exactly the two possible
point-kernel intersections with the marked characteristic middle subgroup. -/
theorem binary_three_source_five_kernel_dichotomy
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
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 5 2)
    :
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let D := Q ⊓ centralizer (Phi : Set G)
    let R := Q ⊓ (centralizer ({z} : Set G)).pCoreIn 2
    R=D ∨ (R ⊓ D=Phi ∧ R ⊔ D=Q) := by
  let C := centralizer ({z} : Set G)
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let R := Q ⊓ C.pCoreIn 2
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hQC : Q ≤ C := hQL.trans hLC
  have hLQ : c.L ≤ normalizer Q := c.L.le_normalizer.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hPhiR : Phi ≤ R := le_inf (map_subtype_le _) (binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inr rfl) hm)
  obtain ⟨em,_,hd,ht⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  let a := linearThreeActor em
  obtain ⟨l,hl⟩ := (em.surjective.comp (QuotientGroup.mk'_surjective _)) singer
  change a l=singer at hl
  have hcQ : Nat.card Q=1048576 := (binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.1
  have hcPhi : Nat.card Phi=256 := by
    rw [show Phi=(frattini Q).map Q.subtype from rfl,card_map_of_injective Q.subtype_injective]
    exact (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.1
  have hcR : Nat.card R=16384 := (binary_three_source_binary_core_sizes
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inr rfl) hm).2
  have hcD : Nat.card D=16384 := by
    have hh : Nat.card Q=Nat.card (Vector × Vector)*Nat.card D := section_card ht
    have hv : Nat.card (Vector × Vector)=64 := by
      simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    rw [hv,hcQ] at hh
    omega
  have hrows := binary_three_source_five_core_image_action
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm em
  rcases hrows with ⟨j,hj⟩ | ⟨j,hj⟩
  · obtain ⟨p,_,hp,he⟩ := image_coordinates C c.L Q hLC hQC a (W.prod W) j hj
    have hDR : D ≤ R := natural_kernel_contains_middle hLQ inf_le_left a hd hPhiR p hp he l hl
    exact Or.inl (eq_of_le_of_card_ge hDR (by omega)).symm
  · obtain ⟨p,hps,hp,he⟩ := image_coordinates C c.L Q hLC hQC a (W.dual.prod W.dual) j hj
    have hsup : R ⊔ D=Q := dual_kernel_sup_middle hLQ a ht inf_le_left p hps hp he l hl
    have hRD : D ≤ normalizer R := by
      have hCN : C ≤ normalizer (C.pCoreIn 2) := C.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
      have hQR : Q ≤ normalizer R :=
        (le_inf Q.le_normalizer (hQC.trans hCN)).trans inf_normalizer_le_normalizer_inf
      exact inf_le_left.trans hQR
    have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes R D hRD
    rw [hcR,hcD,hsup,hcQ] at hcard
    have hPhii : Phi ≤ R ⊓ D := le_inf hPhiR hd.1
    have heq : Phi=R ⊓ D := eq_of_le_of_card_ge hPhii (by omega)
    exact Or.inr ⟨heq.symm,hsup⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
