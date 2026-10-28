module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPointCentralizers
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryParameters
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# The symmetric-three quotient of a paired-plane centralizer

Fixing a natural vector v and a dual vector f with f(v)=1 leaves the
full binary linear group on ker(f). Restriction to that two-space is
bijective: every automorphism extends by fixing v. Its three nonzero
vectors identify the group with S₃, without enumerating SL₃(2).

The original marked component and automizer transport this isomorphism
to the pointwise centralizer of the actual ambient paired plane. The
quotient map retains its literal kernel C_G(W) inside N_G(W) ∩ C_G(U).
The image has trivial two-core; identification of the core of its local
preimage and ambient containment remain separate source obligations.
The actual chosen-module application is in
`NonFFSourceDoubledBinaryPlaneQuotient`.
Source: Aschbacher–Smith §7.7.2, printed p.704, in `refs/quasithin.pdf`.
-/

open Subgroup Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient

def pairFixer (v : Vector) (f : Module.Dual (ZMod 2) Vector) : Subgroup Group :=
  doubledBinaryVectorFixer W v ⊓ doubledBinaryVectorFixer W.dual f

private theorem preserve_form {v : Vector} {f : Module.Dual (ZMod 2) Vector}
    (g : pairFixer v f) (x : Vector) : f (W g x) = f x := by
  have h := LinearMap.congr_fun g.property.2 (W g x)
  change f (W (g : Group)⁻¹ (W g x)) = f (W g x) at h
  rw [Representation.inv_self_apply] at h
  exact h.symm

private def restriction (v : Vector) (f : Module.Dual (ZMod 2) Vector) :
    pairFixer v f →* (f.ker ≃ₗ[ZMod 2] f.ker) where
  toFun g := {
    toFun x := ⟨W g x, by change f (W g x) = 0; rw [preserve_form]; exact x.property⟩
    invFun x := ⟨W (g⁻¹ : pairFixer v f) x, by
      change f (W (g⁻¹ : pairFixer v f) x) = 0
      rw [preserve_form]; exact x.property⟩
    left_inv x := Subtype.ext (Representation.inv_self_apply W g x)
    right_inv x := Subtype.ext (Representation.self_inv_apply W g x)
    map_add' x y := Subtype.ext (map_add (W g) (x : Vector) (y : Vector))
    map_smul' c x := Subtype.ext (map_smul (W g) c (x : Vector)) }
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun l : Module.End (ZMod 2) Vector => l x) W.map_one
  map_mul' a b := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun l : Module.End (ZMod 2) Vector => l x) (W.map_mul a b)

private def split (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hv : f v = 1) :
    Vector ≃ₗ[ZMod 2] (ZMod 2 × f.ker) where
  toFun x := (f x, ⟨x - f x • v, by simp [hv]⟩)
  invFun p := p.1 • v + p.2.val
  left_inv x := by dsimp; abel
  right_inv p := by
    apply Prod.ext
    · simp [hv]
    · apply Subtype.ext
      simp [hv]
  map_add' x y := by
    apply Prod.ext (f.map_add x y)
    apply Subtype.ext
    change (x+y) - f (x+y) • v = (x-f x • v) + (y-f y • v)
    rw [map_add,add_smul]
    abel
  map_smul' c x := by
    apply Prod.ext (f.map_smul c x)
    apply Subtype.ext
    simp [smul_sub,smul_smul]

private theorem restriction_injective (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1) :
    Function.Injective (restriction v f) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  let y : f.ker := ⟨x - f x • v, by simp [hfv]⟩
  have hy : W a y = W b y := congrArg Subtype.val (LinearEquiv.congr_fun hab y)
  have hx : x = f x • v + y.val := by dsimp [y]; abel
  change W a x = W b x
  rw [hx,map_add,map_smul,map_add,map_smul,a.property.1,b.property.1,hy]

private theorem restriction_surjective (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1) : Function.Surjective (restriction v f) := by
  intro e
  let s := split v f hfv
  let a := s.trans (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr e).trans s.symm)
  have hform (x : Vector) : f (a x) = f x := by
    exact congrArg Prod.fst (s.apply_symm_apply _)
  have hvec : a v = v := by
    apply s.injective
    change s (s.symm _) = s v
    rw [s.apply_symm_apply]
    have hs : s v = (1,0) := by
      apply Prod.ext hfv
      apply Subtype.ext
      simp [s,split,hfv]
    change ((s v).1, e (s v).2) = s v
    rw [hs]
    simp
  let g : Group := ⟨LinearMap.toMatrix' a.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ a.isUnit_det'.ne_zero⟩
  have hg (x : Vector) : W g x = a x := by
    change Matrix.toLin' (LinearMap.toMatrix' a.toLinearMap) x = a x
    rw [Matrix.toLin'_toMatrix']
    rfl
  have hgp : g ∈ pairFixer v f := by
    constructor
    · exact (hg v).trans hvec
    · apply LinearMap.ext
      intro x
      change f (W g⁻¹ x) = f x
      rw [← hform (W g⁻¹ x),← hg,Representation.self_inv_apply]
  refine ⟨⟨g,hgp⟩,?_⟩
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  change W g x = (e x).val
  rw [hg]
  change s.symm (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr e) (s x)) = _
  have hs : s x = (0,x) := by
    apply Prod.ext
    · exact x.property
    · apply Subtype.ext
      change (x : Vector) - f x • v = (x : Vector)
      rw [show f x = 0 from x.property,zero_smul,sub_zero]
  rw [hs]
  change (0 : ZMod 2) • v + (e x).val = _
  simp

/-- The pointwise fixer of a natural vector and a dual vector of pairing one
is the full linear group on the dual kernel, hence S₃. -/
def pairEquivSymmetric (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1) : pairFixer v f ≃* Equiv.Perm (Fin 3) := by
  have hf : f ≠ 0 := by intro he; simp [he] at hfv
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hv : Module.finrank (ZMod 2) Vector = 3 := by
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  have hp : Module.finrank (ZMod 2) BinaryFourPlus.Plane = 2 := by simp [BinaryFourPlus.Plane]
  let b : f.ker ≃ₗ[ZMod 2] BinaryFourPlus.Plane := LinearEquiv.ofFinrankEq _ _ (by omega)
  let c : (f.ker ≃ₗ[ZMod 2] f.ker) ≃* (BinaryFourPlus.Plane ≃ₗ[ZMod 2] BinaryFourPlus.Plane) := {
    toFun e := b.symm.trans (e.trans b)
    invFun e := b.trans (e.trans b.symm)
    left_inv e := by ext x; simp
    right_inv e := by ext x; simp
    map_mul' e d := by ext x; simp }
  exact (MulEquiv.ofBijective (restriction v f)
    ⟨restriction_injective v f hfv,restriction_surjective v f hfv⟩).trans
      (c.trans BinaryFourPlus.planeAutEquiv)


open ChapterE DoubledBinaryPlanes

private theorem ambientPlane_fixer_iff
    {G : Type*} [_root_.Group G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (n : normalizer (W₀ : Set G)) :
    (n : G) ∈ centralizer (ambientPlane W₀ E v f : Set G) ↔
      automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n) (E.symm (v,0)) = E.symm (v,0) ∧
      automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n) (E.symm (0,f)) = E.symm (0,f) := by
  have hfix (w : Additive W₀) : (w.toMul : G) ∈ centralizer ({(n : G)} : Set G) ↔
      automizerRepresentation W₀ (W₀.normalizerMonoidHom.rangeRestrict n) w = w := by
    constructor
    · intro hh
      apply Additive.toMul.injective
      apply Subtype.ext
      change (n : G) * (w.toMul : G) * (n : G)⁻¹ = (w.toMul : G)
      rw [hh _ (Set.mem_singleton _),mul_inv_cancel_right]
    · intro hh z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      have he := congrArg (fun x : Additive W₀ => (x.toMul : G)) hh
      change (n : G) * (w.toMul : G) * (n : G)⁻¹ = (w.toMul : G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
  rw [← hfix,← hfix,← ambientPlane_le_iff]
  constructor
  · intro hn x hx y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact (hn x hx).symm
  · intro hp x hx
    exact (hp hx _ (Set.mem_singleton _)).symm

/-- The actual paired-plane centralizer has symmetric-three image in the
whole-orbit automizer, with the original marking retained. -/
theorem ambientPlane_equiv
    {G : Type*} [_root_.Group G] (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) =
        NaturalDual.action (q l) (E w))
    (a : Automizer W₀ ≃* MulAut Group)
    (ha : ∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (NaturalDual.action g (E w)))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W₀ b w)))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    Nonempty (inducedAutomizer W₀ (centralizer (ambientPlane W₀ E v f : Set G)) ≃*
      Equiv.Perm (Fin 3)) := by
  let P := inducedAutomizer W₀ (centralizer (ambientPlane W₀ E v f : Set G))
  have hinner (b : P) : a b ∈ MulAut.innerSubgroup Group := by
    obtain ⟨n,hn,he⟩ := b.property
    rw [← he]
    exact doubledBinary_ambientPlane_fixer_inner W₀ E a hcov n v f hfv hn
  let c : Group ≃* MulAut.innerSubgroup Group :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)
  let j : P →* Group := c.symm.toMonoidHom.comp
    ((a.toMonoidHom.comp P.subtype).codRestrict _ hinner)
  have hj (b : P) : MulAut.conj (j b) = a b :=
    congrArg Subtype.val (c.apply_symm_apply _)
  have hact (b : P) (w : Additive W₀) :
      E (automizerRepresentation W₀ b w) = NaturalDual.action (j b) (E w) := by
    obtain ⟨l,hl⟩ := hq (j b)
    have he : W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l) = b :=
      a.injective (by rw [ha,hl,hj])
    rw [← he,hE,hl]
  have hfix (b : P) :
      automizerRepresentation W₀ b (E.symm (v,0)) = E.symm (v,0) ∧
      automizerRepresentation W₀ b (E.symm (0,f)) = E.symm (0,f) := by
    obtain ⟨n,hn,he⟩ := b.property
    rw [← he]
    exact (ambientPlane_fixer_iff W₀ E v f n).mp hn
  have hjp (b : P) : j b ∈ pairFixer v f := by
    have hn := hact b (E.symm (v,0))
    rw [(hfix b).1,E.apply_symm_apply] at hn
    have hd := hact b (E.symm (0,f))
    rw [(hfix b).2,E.apply_symm_apply] at hd
    exact ⟨(congrArg Prod.fst hn).symm,(congrArg Prod.snd hd).symm⟩
  let k : P →* pairFixer v f := j.codRestrict _ hjp
  have hki : Function.Injective k := by
    intro b d he
    apply Subtype.ext
    apply a.injective
    rw [← hj,← hj]
    exact congrArg MulAut.conj (congrArg Subtype.val he)
  have hks : Function.Surjective k := by
    intro g
    obtain ⟨l,hl⟩ := hq g
    have hn : (l : G) ∈ centralizer (ambientPlane W₀ E v f : Set G) := by
      apply (ambientPlane_fixer_iff W₀ E v f (inclusion hLN l)).mpr
      constructor
      · apply E.injective
        rw [hE,hl,E.apply_symm_apply]
        exact Prod.ext g.property.1 (map_zero (W.dual g))
      · apply E.injective
        rw [hE,hl,E.apply_symm_apply]
        exact Prod.ext (map_zero (W g)) g.property.2
    let b : P := ⟨W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l),
      ⟨inclusion hLN l,hn,rfl⟩⟩
    refine ⟨b,?_⟩
    apply Subtype.ext
    apply MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
    exact (hj b).trans ((ha l).trans (congrArg MulAut.conj hl))
  exact ⟨(MulEquiv.ofBijective k ⟨hki,hks⟩).trans (pairEquivSymmetric v f hfv)⟩

/-- The original local centralizer surjects onto its induced automizer, with
kernel the intersection with the whole-orbit centralizer. -/
theorem centralizer_quotient
    {G H : Type*} [_root_.Group G] [_root_.Group H]
    (W₀ U : Subgroup G)
    (he : Nonempty (inducedAutomizer W₀ (centralizer (U : Set G)) ≃* H)) :
    ∃ π : (normalizer (W₀ : Set G) ⊓ centralizer (U : Set G) : Subgroup G) →* H,
      Function.Surjective π ∧ π.ker = (centralizer (W₀ : Set G)).subgroupOf
        (normalizer (W₀ : Set G) ⊓ centralizer (U : Set G)) := by
  obtain ⟨e⟩ := he
  let C := normalizer (W₀ : Set G) ⊓ centralizer (U : Set G)
  let P := inducedAutomizer W₀ (centralizer (U : Set G))
  let q := W₀.normalizerMonoidHom.rangeRestrict.comp
    (inclusion (show C ≤ normalizer (W₀ : Set G) from inf_le_left))
  have hq (c : C) : q c ∈ P := ⟨inclusion inf_le_left c,c.property.2,rfl⟩
  let p : C →* P := q.codRestrict P hq
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨n,hn,he⟩ := b.property
    exact ⟨⟨n,n.property,hn⟩,Subtype.ext he⟩
  refine ⟨e.toMonoidHom.comp p,e.surjective.comp hp,?_⟩
  ext c
  change e (p c) = 1 ↔ (c : G) ∈ centralizer (W₀ : Set G)
  rw [← e.map_one,e.injective.eq_iff]
  have he : p c = 1 ↔ W₀.normalizerMonoidHom (inclusion inf_le_left c) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun x : P => x.val.val) hh
    · intro hh
      exact Subtype.ext (Subtype.ext hh)
  rw [he]
  change inclusion inf_le_left c ∈ W₀.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- The induced paired-plane actor has trivial two-core; this does not assert
that its full ambient preimage is a two-group. -/
theorem twoCore_eq_bot_of_symmetricThree
    {H : Type*} [_root_.Group H] [Finite H]
    (he : Nonempty (H ≃* Equiv.Perm (Fin 3))) : pCore 2 H = ⊥ := by
  obtain ⟨e⟩ := he
  have hk : e.toMonoidHom.ker = ⊥ := e.toMonoidHom.ker_eq_bot e.injective
  exact (ker_eq_twoCore_of_surjective_perm_three e.toMonoidHom e.surjective
    (hk ▸ IsPGroup.of_bot)).symm.trans hk

private theorem pairedPlane_finrank (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1) : Module.finrank (ZMod 2) (pairedPlane v f) = 2 := by
  have hv : v ≠ 0 := by intro he; simp [he] at hfv
  have hf : f ≠ 0 := by intro he; simp [he] at hfv
  let d := (LinearMap.toSpanSingleton (ZMod 2) Vector v).prodMap
    (LinearMap.toSpanSingleton (ZMod 2) (Module.Dual (ZMod 2) Vector) f)
  have hi : Function.Injective d := by
    intro x y he
    apply Prod.ext
    · exact (smul_left_injective (ZMod 2) hv) (congrArg Prod.fst he)
    · exact (smul_left_injective (ZMod 2) hf) (congrArg Prod.snd he)
  have hr : d.range = pairedPlane v f := by
    apply le_antisymm
    · rintro x ⟨p,rfl⟩
      have hh := (pairedPlane_le_iff v f (pairedPlane v f)).mp le_rfl
      have he : d p = p.1 • (v,0) + p.2 • (0,f) := by
        apply Prod.ext <;> simp [d]
      rw [he]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hh.1) (Submodule.smul_mem _ _ hh.2)
    · rw [pairedPlane_le_iff]
      constructor
      · exact ⟨(1,0),by simp [d]⟩
      · exact ⟨(0,1),by simp [d]⟩
  rw [← hr,← (LinearEquiv.ofInjective d hi).finrank_eq]
  simp [Module.finrank_prod]

/-- Every paired plane in the original orbit is an actual four-group. -/
theorem ambientPlane_card
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    Nat.card (ambientPlane W₀ E v f) = 4 := by
  let U := (pairedPlane v f).comap E.toLinearMap
  have he : U.map E.toLinearMap = pairedPlane v f :=
    Submodule.map_comap_eq_of_surjective E.surjective _
  have hd := (Submodule.equivMapOfInjective E.toLinearMap E.injective U).finrank_eq
  rw [he,pairedPlane_finrank v f hfv] at hd
  have hp := (pairedPlane_le_iff v f (pairedPlane v f)).mp le_rfl
  have hplane : ambientPlane W₀ E v f = ambientSubmodule W₀ U := by
    apply le_antisymm
    · rw [ambientPlane_le_iff]
      constructor
      · refine ⟨(E.symm (v,0)).toMul,?_,rfl⟩
        change E (E.symm (v,0)) ∈ pairedPlane v f
        rw [E.apply_symm_apply]
        exact hp.1
      · refine ⟨(E.symm (0,f)).toMul,?_,rfl⟩
        change E (E.symm (0,f)) ∈ pairedPlane v f
        rw [E.apply_symm_apply]
        exact hp.2
    · let Z := (moduleSubgroup W₀).symm ((ambientPlane W₀ E v f).subgroupOf W₀)
      have hg := (ambientPlane_le_iff W₀ E v f (ambientPlane W₀ E v f)).mp le_rfl
      have hz : pairedPlane v f ≤ Z.map E.toLinearMap := by
        rw [pairedPlane_le_iff]
        exact ⟨⟨E.symm (v,0),hg.1,E.apply_symm_apply _⟩,
          ⟨E.symm (0,f),hg.2,E.apply_symm_apply _⟩⟩
      rintro x ⟨w,hw,rfl⟩
      change E (Additive.ofMul w) ∈ pairedPlane v f at hw
      have hm := hz hw
      rw [Submodule.mem_map_equiv,E.symm_apply_apply] at hm
      exact hm
  rw [hplane]
  change Nat.card ((moduleSubgroup W₀ U).map W₀.subtype) = 4
  rw [Subgroup.card_map_of_injective W₀.subtype_injective]
  change Nat.card U = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  rfl

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient
