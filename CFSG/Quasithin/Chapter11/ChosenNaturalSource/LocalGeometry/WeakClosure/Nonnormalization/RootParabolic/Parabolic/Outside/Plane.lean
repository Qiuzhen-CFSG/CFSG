module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Parabolic.Proper

/-!
# The actual plane action and its two centralizer indices

A nontrivial elementary field-linear action on a plane fixing a field line
has that line as both its fixed space and displacement space. Evaluation at
one vector off the line bounds the faithful actor by the field order.
E.3.7 gives the reverse bound for an actual conjugate of V.

The restricted original quotient map identifies both ambient centralizer
indices and the commutator modulo the whole C_V(L). Fixed-point lifting is
an explicit interface here; the natural-row consumer proves it, including
on the nonsplit symplectic cover.

Source: Aschbacher--Smith, 11.2.4, printed p.769; E.3.7, printed p.232.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Subgroup Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Outside
variable {F X : Type*} [Field F] [AddCommGroup X] [Module F X]
    [FiniteDimensional F X]

private theorem end_eq_one_of_fixes_line_and_vector
    (hd : Module.finrank F X=2) (P : Submodule F X) (hP : Module.finrank F P=1)
    (a : Module.End F X) (hfix : ∀x∈P,a x=x)
    (x:X) (hx:x∉P) (hax:a x=x) : a=1 := by
  let K := (a-1).ker
  have hPK : P≤K := by
    intro v hv
    change a v-v=0
    exact sub_eq_zero.mpr (hfix v hv)
  have hxK : x∈K := by
    change a x-x=0
    exact sub_eq_zero.mpr hax
  have hK : K=⊤ := by
    by_contra hn
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hn)
    rw [finrank_top,hd] at hlt
    have hlo := Submodule.finrank_mono hPK
    rw [hP] at hlo
    have he : P=K := Submodule.eq_of_le_of_finrank_eq hPK (by omega)
    exact hx (he.symm ▸ hxK)
  ext v
  have hv : v∈K := by rw [hK]; trivial
  exact sub_eq_zero.mp hv

private theorem plane_involution_displacement [Module (ZMod 2) X]
    (hd : Module.finrank F X=2) (P : Submodule F X) (hP : Module.finrank F P=1)
    (a : Module.End F X) (hfix : ∀x∈P,a x=x) (hsq : a*a=1) (x:X) :
    a x-x∈P := by
  by_contra hn
  have hneg (v:X) : -v=v := by
    have hh : v+v=0 := ZModModule.add_self v
    exact neg_eq_iff_add_eq_zero.mpr hh
  have hy : a (a x-x)=a x-x := by
    rw [map_sub,←Module.End.mul_apply,hsq]
    change x-a x=a x-x
    simp only [sub_eq_add_neg,hneg]
    exact add_comm _ _
  have he := end_eq_one_of_fixes_line_and_vector hd P hP a hfix (a x-x) hn hy
  rw [he] at hn
  exact hn (by simp)

private theorem plane_invariants_eq_line
    {A : Type*} [Group A] (ρ : Representation F A X)
    (hd : Module.finrank F X=2) (P : Submodule F X) (hP : Module.finrank F P=1)
    (hfix : ∀a, ∀x∈P,ρ a x=x)
    (hne : ∃a x,ρ a x≠x) : ρ.invariants=P := by
  apply le_antisymm
  · intro x hx
    by_contra hn
    obtain ⟨a,v,hv⟩ := hne
    have he := end_eq_one_of_fixes_line_and_vector hd P hP (ρ a) (hfix a) x hn (hx a)
    exact hv (LinearMap.congr_fun he v)
  · intro x hx a
    exact hfix a x hx

private theorem plane_displacement_eq_line [Module (ZMod 2) X]
    {A : Type*} [Group A] (ρ : Representation F A X)
    (hd : Module.finrank F X=2) (P : Submodule F X) (hP : Module.finrank F P=1)
    (hfix : ∀a, ∀x∈P,ρ a x=x) (hsq : ∀a:A,a^2=1)
    (hne : ∃a x,ρ a x≠x) : Coinvariants.ker ρ=P := by
  have hle : Coinvariants.ker ρ≤P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,x⟩,rfl⟩
    exact plane_involution_displacement hd P hP (ρ a) (hfix a)
      (by rw [←map_mul,←pow_two,hsq,map_one]) x
  have hn : Coinvariants.ker ρ≠⊥ := by
    intro hz
    obtain ⟨a,x,hx⟩ := hne
    have h := Coinvariants.sub_mem_ker (ρ := ρ) a x
    rw [hz,Submodule.mem_bot] at h
    exact hx (sub_eq_zero.mp h)
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hlo : Module.finrank F (Coinvariants.ker ρ)≠0 :=
    fun hz => hn (Submodule.finrank_eq_zero.mp hz)
  have hhi := Submodule.finrank_mono hle
  omega

private theorem plane_actor_card_le_field [Module (ZMod 2) X] [Finite F]
    {A : Type*} [Group A] (ρ : Representation F A X)
    (hd : Module.finrank F X=2) (P : Submodule F X) (hP : Module.finrank F P=1)
    (hfix : ∀a, ∀x∈P,ρ a x=x) (hsq : ∀a:A,a^2=1) :
    Nat.card ((ρ.asGroupHom).range)≤Nat.card F := by
  let : Finite X := Module.finite_of_finite F
  have hPtop : P≠⊤ := by
    intro he
    rw [he,finrank_top,hd] at hP
    omega
  obtain ⟨x,hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hPtop)
  have hxP : x∉P := hx.2
  let j : (ρ.asGroupHom).range → P := fun a => ⟨(a.val : Module.End F X) x-x,by
    obtain ⟨b,hb⟩ := a.property
    rw [←hb]
    exact plane_involution_displacement hd P hP (ρ b) (hfix b)
      (by rw [←map_mul,←pow_two,hsq,map_one]) x⟩
  have hj : Function.Injective j := by
    rintro ⟨_,⟨a,rfl⟩⟩ ⟨_,⟨b,rfl⟩⟩ he
    apply Subtype.ext
    apply Units.ext
    change ρ a=ρ b
    have he' : ρ a x-x=ρ b x-x := congrArg Subtype.val he
    have hv : ρ a x=ρ b x := sub_left_injective he'
    have hc : ρ (b⁻¹*a) x=x := by
      rw [map_mul,Module.End.mul_apply,hv,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]
      rfl
    have hid := end_eq_one_of_fixes_line_and_vector hd P hP (ρ (b⁻¹*a)) (hfix _) x hxP hc
    have hh := congrArg (fun t : Module.End F X => ρ b*t) hid
    simpa only [←map_mul,mul_inv_cancel_left,mul_one] using hh
  have hc := Nat.card_le_card_of_injective j hj
  have hcard : Nat.card P=Nat.card F := by
    rw [Module.natCard_eq_pow_finrank (K := F),hP,pow_one]
  rw [hcard] at hc
  exact hc


open Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private def subspaceProjection (c : Coordinates D S.field) (P : Submodule S.field.Carrier c.Space) :
    c.preimage P →* Multiplicative P where
  toFun v := Multiplicative.ofAdd ⟨(c.projection ⟨v,D.centralQuotientPreimage_le _ v.property⟩).toAdd,
    (c.mem_preimage P ⟨v,D.centralQuotientPreimage_le _ v.property⟩).mp v.property⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (c.projection 1).toAdd=0
    rw [map_one]
    rfl
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (c.projection (⟨v,D.centralQuotientPreimage_le _ v.property⟩ *
      ⟨w,D.centralQuotientPreimage_le _ w.property⟩)).toAdd=_
    rw [map_mul]
    rfl

private theorem subspaceProjection_surjective (c : Coordinates D S.field)
    (P : Submodule S.field.Carrier c.Space) : Function.Surjective (subspaceProjection c P) := by
  intro x
  obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x.toAdd.val)
  have hvP : (v:G)∈c.preimage P := (c.mem_preimage P v).mpr (by
    change (c.projection v).toAdd∈P
    rw [hv]
    exact x.toAdd.property)
  refine ⟨⟨v,hvP⟩,?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hv

private theorem subspaceProjection_ker_map (c : Coordinates D S.field)
    (P : Submodule S.field.Carrier c.Space) :
    (subspaceProjection c P).ker.map (c.preimage P).subtype=V ⊓ centralizer (L:Set G) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨D.centralQuotientPreimage_le _ w.property,?_⟩
    apply (c.projection_eq_one_iff ⟨w,D.centralQuotientPreimage_le _ w.property⟩).mp
    apply Multiplicative.toAdd.injective
    exact congrArg (fun x : Multiplicative P => x.toAdd.val) hw
  · intro hv
    have hvP : v∈c.preimage P := by
      apply ((c.preimage_le_iff ⊥ P).mpr bot_le)
      rwa [c.preimage_bot]
    refine ⟨⟨v,hvP⟩,?_,rfl⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((c.projection_eq_one_iff ⟨v,hv.1⟩).mpr hv.2)

private theorem subspaceProjection_centralizer_kernel
    {c : Coordinates D S.field} (P : Submodule S.field.Carrier c.Space)
    {A : Subgroup G} (ρ : Representation S.field.Carrier A P)
    (hfixed : ∀ (a:A) (v:c.preimage P),
      ρ a (subspaceProjection c P v).toAdd=(subspaceProjection c P v).toAdd ↔
        (a:G)*(v:G)=(v:G)*(a:G)) :
    ρ.asGroupHom.ker=(centralizer (c.preimage P:Set G)).subgroupOf A := by
  ext a
  constructor
  · intro ha
    apply mem_centralizer_iff.mpr
    intro v hv
    have he : ρ a=1 := congrArg Units.val ha
    exact ((hfixed a ⟨v,hv⟩).mp (by rw [he]; rfl)).symm
  · intro ha
    apply Units.ext
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv⟩ := subspaceProjection_surjective c P (Multiplicative.ofAdd x)
    have he := (hfixed a v).mpr (mem_centralizer_iff.mp ha v.val v.property).symm
    rw [hv] at he
    exact he

private theorem subspaceProjection_actor_card
    {c : Coordinates D S.field} (P : Submodule S.field.Carrier c.Space)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (ρ : Representation S.field.Carrier A P)
    (hfixed : ∀ (a:A) (v:c.preimage P),
      ρ a (subspaceProjection c P v).toAdd=(subspaceProjection c P v).toAdd ↔
        (a:G)*(v:G)=(v:G)*(a:G)) :
    Nat.card ρ.asGroupHom.range=
      2^subgroupCorank A (A ⊓ centralizer (c.preimage P:Set G)) := by
  rw [←index_ker,subspaceProjection_centralizer_kernel P ρ hfixed]
  change (centralizer (c.preimage P:Set G)).relIndex A=_
  rw [←inf_relIndex_left A,relIndex_eq_two_pow_quotient_finrank,
    ←subgroupCorank_eq_quotient_finrank]


theorem small_action_of_plane_action {c : Coordinates D S.field}
    (f : InvariantFlag c) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    [IsElementaryAbelian 2 V] (hs : globalS V=S.field.degree)
    (ρ : Representation S.field.Carrier (V.map (MulAut.conj g).toMonoidHom) c.Space)
    (hρ : ∀ a v, ρ a (c.projection v).toAdd =
      (c.projection (V.normalizerMonoidHom (inclusion (hg.trans S.sylow_normalizes) a) v)).toAdd)
    (hpoint : ∀ a x, x∈f.space 0 → ρ a x=x)
    (hlift : ∀ a v, ρ a (c.projection v).toAdd=(c.projection v).toAdd ↔
      (a:G)*(v:G)=(v:G)*(a:G))
    (hne : ⁅f.Vi 1,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) (f.Vi 1) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let P := f.space 1
  let W := c.preimage P
  let Q := (f.space 0).comap P.subtype
  let p : W →* Multiplicative P := subspaceProjection c P
  letI : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  letI : Finite c.Space := Finite.of_surjective
    (fun v:V => (c.projection v).toAdd) (Multiplicative.toAdd.surjective.comp c.projection_surjective)
  letI : FiniteDimensional S.field.Carrier c.Space := Module.Finite.of_finite
  have hinv : ∀a:A,P≤P.comap (ρ a) := by
    intro a x hx
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    have hvP : (v:G)∈W := (c.mem_preimage P v).mpr (by
      change (c.projection v).toAdd∈P
      rw [hv]
      exact hx)
    have hn := f.invariant 1 (hg a.property)
    have hm := (mem_normalizer_iff.mp hn) v.val
    have hw : ((a:G)*(v:G)*(a:G)⁻¹)∈W := hm.mp hvP
    have hh := (c.mem_preimage P
      (V.normalizerMonoidHom (inclusion (hg.trans S.sylow_normalizes) a) v)).mp hw
    change (c.projection (V.normalizerMonoidHom (inclusion (hg.trans S.sylow_normalizes) a) v)).toAdd∈P at hh
    rw [←hρ,hv] at hh
    exact hh
  let τ := ρ.subrepresentation P hinv
  have hd : Module.finrank S.field.Carrier P=2 := f.dimension 1
  have hQ : Module.finrank S.field.Carrier Q=1 := by
    have he : Q.map P.subtype=f.space 0 := by
      rw [Submodule.map_comap_eq,Submodule.range_subtype]
      exact inf_eq_right.mpr (f.nested (by decide : (0:Fin 3)≤1))
    rw [←Submodule.finrank_map_subtype_eq P Q,he]
    exact f.dimension 0
  have hfix : ∀a:A, ∀x∈Q,τ a x=x := by
    intro a x hx
    apply Subtype.ext
    exact hpoint a x hx
  have hsq : ∀a:A,a^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A)
  have hfixed : ∀ (a:A) (v:W), τ a (p v).toAdd=(p v).toAdd ↔
      (a:G)*(v:G)=(v:G)*(a:G) := by
    intro a v
    exact (Subtype.ext_iff).trans (hlift a ⟨v,D.centralQuotientPreimage_le _ v.property⟩)
  have hn : ∃a x,τ a x≠x := by
    by_contra h
    push Not at h
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv a ha
    exact ((hfixed ⟨a,ha⟩ ⟨v,hv⟩).mp (h _ _))
  have hdisp := plane_displacement_eq_line τ hd Q hQ hfix hsq hn
  have hfixedSpace := plane_invariants_eq_line τ hd Q hQ hfix hn
  have hactor : subgroupCorank A (A ⊓ centralizer (W:Set G))=S.field.degree := by
    have hc := plane_actor_card_le_field τ hd Q hQ hfix hsq
    rw [subspaceProjection_actor_card P τ hfixed,S.field.card_eq] at hc
    have hu : subgroupCorank A (A ⊓ centralizer (W:Set G))≤S.field.degree :=
      (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc
    exact le_antisymm hu (actor_corank_lower_of_noncentral hs g hg W
      (D.centralQuotientPreimage_le _) hne)
  have hcentral : W ⊓ centralizer (A:Set G)=f.Vi 0 := by
    apply le_antisymm
    · intro v hv
      apply (c.mem_preimage _ ⟨v,D.centralQuotientPreimage_le _ hv.1⟩).mpr
      have hh : (p ⟨v,hv.1⟩).toAdd∈τ.invariants := by
        intro a
        exact (hfixed a ⟨v,hv.1⟩).mpr (mem_centralizer_iff.mp hv.2 a.val a.property)
      rw [hfixedSpace] at hh
      exact hh
    · intro v hv
      have hvW : v∈W := (c.preimage_le_iff _ _).mpr (f.nested (by decide)) hv
      refine ⟨hvW,mem_centralizer_iff.mpr ?_⟩
      intro a ha
      exact ((hfixed ⟨a,ha⟩ ⟨v,hvW⟩).mp (hfix _ _
        ((c.mem_preimage _ ⟨v,D.centralQuotientPreimage_le _ hv⟩).mp hv)))
  have hvector : subgroupCorank W (W ⊓ centralizer (A:Set G))=S.field.degree := by
    have he : (f.Vi 0).subgroupOf W=Q.toAddSubgroup.toSubgroup.comap p := by
      ext v
      exact c.mem_preimage _ ⟨v,D.centralQuotientPreimage_le _ v.property⟩
    rw [hcentral,subgroupCorank,relIndex,he,index_comap_of_surjective _
      (show Function.Surjective p from subspaceProjection_surjective c P),AddSubgroup.index_toSubgroup]
    change Nat.log 2 (Nat.card (P ⧸ Q))=S.field.degree
    have hdim := Submodule.finrank_quotient_add_finrank Q
    have hdim' : Module.finrank S.field.Carrier (P ⧸ Q)=1 := by omega
    rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier),hdim',pow_one,S.field.card_eq,
      Nat.log_pow Nat.one_lt_two]
  refine ⟨D.centralQuotientPreimage_le _,?_,hactor,hvector⟩
  have hmove : ∀ a (v:W), (ρ a (c.projection ⟨v,D.centralQuotientPreimage_le _ v.property⟩).toAdd -
      (c.projection ⟨v,D.centralQuotientPreimage_le _ v.property⟩).toAdd)∈f.space 0 := by
    intro a v
    exact plane_involution_displacement hd Q hQ (τ a) (hfix a)
      (by rw [←map_mul,←pow_two,hsq,map_one]) (p v).toAdd
  apply le_antisymm
  · apply sup_le
    · rw [commutator_comm]
      apply commutator_le.mpr
      intro a ha v hv
      let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
      let w : V := V.normalizerMonoidHom (inclusion (hg.trans S.sylow_normalizes) ⟨a,ha⟩) v'*v'⁻¹
      change (w:G)∈f.Vi 0
      apply (c.mem_preimage _ w).mpr
      change (c.projection (V.normalizerMonoidHom _ v'*v'⁻¹)).toAdd∈f.space 0
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,←hρ]
      exact hmove ⟨a,ha⟩ ⟨v,hv⟩
    · rw [←c.preimage_bot]
      exact (c.preimage_le_iff _ _).mpr bot_le
  · have hspan : ∀ x∈Coinvariants.ker τ, ∀ r:S.field.Carrier,
        ∃ v:W, (v:G)∈⁅W,A⁆ ∧ (p v).toAdd=r • x := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨a,y⟩,rfl⟩ := hx
        intro r
        obtain ⟨v,hv⟩ := subspaceProjection_surjective c P (Multiplicative.ofAdd (r • y))
        let w : W := W.normalizerMonoidHom (inclusion (hg.trans (f.invariant 1)) a) v*v⁻¹
        refine ⟨w,?_,?_⟩
        · rw [commutator_comm]
          exact commutator_mem_commutator a.property v.property
        · apply Subtype.ext
          change (c.projection (V.normalizerMonoidHom (inclusion (hg.trans S.sylow_normalizes) a)
            ⟨v,D.centralQuotientPreimage_le _ v.property⟩ *
            (⟨v,D.centralQuotientPreimage_le _ v.property⟩ : V)⁻¹)).toAdd=_
          rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,←hρ]
          have hv' := congrArg (fun z : Multiplicative P => z.toAdd.val) hv
          change (c.projection ⟨v,D.centralQuotientPreimage_le _ v.property⟩).toAdd=r • y.val at hv'
          rw [hv',map_smul,smul_sub]
          rfl
      | zero => intro r; exact ⟨1,one_mem _,by simp⟩
      | add x y hx hy ihx ihy =>
        intro r
        obtain ⟨v,hv,hvx⟩ := ihx r
        obtain ⟨w,hw,hwy⟩ := ihy r
        exact ⟨v*w,mul_mem hv hw,by rw [map_mul,toAdd_mul,hvx,hwy,smul_add]⟩
      | smul r x hx ih => intro s; simpa only [smul_smul] using ih (s*r)
    intro v hv
    have hvW : v∈W := (c.preimage_le_iff _ _).mpr (f.nested (by decide)) hv
    have hx : (p ⟨v,hvW⟩).toAdd∈Coinvariants.ker τ := by
      rw [hdisp]
      exact (c.mem_preimage _ ⟨v,D.centralQuotientPreimage_le _ hv⟩).mp hv
    obtain ⟨w,hw,hwp⟩ := hspan _ hx 1
    simp only [one_smul] at hwp
    have he : p w=p ⟨v,hvW⟩ := Multiplicative.toAdd.injective hwp
    have hk : v*(w:G)⁻¹∈V ⊓ centralizer (L:Set G) := by
      rw [←subspaceProjection_ker_map c P]
      refine ⟨⟨v,hvW⟩*w⁻¹,?_,rfl⟩
      change p (⟨v,hvW⟩*w⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hh := (⁅W,A⁆ ⊔ (V ⊓ centralizer (L:Set G))).mul_mem
      (mem_sup_right hk) (mem_sup_left hw)
    change v∈⁅W,A⁆ ⊔ (V ⊓ centralizer (L:Set G))
    simpa only [inv_mul_cancel_right] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Outside
