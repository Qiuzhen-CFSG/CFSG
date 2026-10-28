module
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.SL2.LineBorelResidual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Recognition.Marking

/-!
# Descent of the literal opposite-core action

The source core commutator puts [O₂(I),I] in Q, which acts trivially on
its elementary quotient Q/N. Remove the common kernel of the marked SL₂
map and this quotient action. The remaining kernel is central, and the
first root maps injectively onto a Sylow subgroup. Its full normalizer
lifts by [V,W]=V₁. The root-normalizer commutator therefore puts both
opposite roots in the derived subgroup. Abelian-Sylow transfer kills the
central two-kernel, including when q=4.

Thus O₂(I) acts trivially on the original Q/((W∩Wʸ)V). No multiplier
vanishing for SL₂(4) or splitting of the original extension is assumed.
Source: Aschbacher--Smith, 11.5.7, printed p.783.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
set_option backward.isDefEq.respectTransparency false
noncomputable section

private theorem central_kernel_trivial
    {H B : Type*} [Group H] [Finite H] [Group B] [Finite B]
    {p : ℕ} [Fact p.Prime]
    (f : H →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center H)
    (hp : IsPGroup p f.ker) (P : Sylow p B) [IsMulCommutative P]
    (U : Subgroup H) (hU : U.map f = P) (hdis : Disjoint U f.ker)
    (hn : (normalizer (P : Set B)).comap f ≤ normalizer (U : Set H))
    (hcomm : ⁅(P : Subgroup B),normalizer (P : Set B)⁆ = P)
    (j : H) (hgen : U ⊔ U.map (MulAut.conj j).toMonoidHom = ⊤) :
    Function.Injective f := by
  let N := (normalizer (P : Set B)).comap f
  have hm : ⁅U,N⁆.map f = U.map f := by
    rw [map_commutator,hU,map_comap_eq_self_of_surjective hf,hcomm]
  have hDU : ⁅U,N⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hn
  have hUD : U ≤ _root_.commutator H := by
    intro u hu
    have hmU : f u ∈ ⁅U,N⁆.map f := hm.ge (mem_map_of_mem f hu)
    obtain ⟨c,hc,he⟩ := hmU
    have hcu : c⁻¹*u ∈ U ⊓ f.ker :=
      ⟨U.mul_mem (U.inv_mem (hDU hc)) hu,by
        change f (c⁻¹*u) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]⟩
    have heq : c = u := inv_mul_eq_one.mp (mem_bot.mp (hdis.le_bot hcu))
    exact heq ▸ (commutator_mono le_top le_top hc)
  have ht : _root_.commutator H = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le hUD ((map_mono hUD).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (((normalizer_eq_top (_root_.commutator H)) ▸ mem_top j))))
  let : Group.IsPerfect H := ⟨ht⟩
  have hUcomm : IsMulCommutative U := by
    refine ⟨⟨fun u v => Subtype.ext ?_⟩⟩
    have hfu : f u ∈ (P : Subgroup B) := hU ▸ mem_map_of_mem f u.property
    have hfv : f v ∈ (P : Subgroup B) := hU ▸ mem_map_of_mem f v.property
    have he : f ((u:H)*(v:H)) = f ((v:H)*(u:H)) := by
      rw [map_mul,map_mul]
      exact congrArg (fun a : P => (a:B))
        (mul_comm (⟨f u,hfu⟩ : P) (⟨f v,hfv⟩ : P))
    have hk : ((u:H)*(v:H))⁻¹ * ((v:H)*(u:H)) ∈ U ⊓ f.ker :=
      ⟨U.mul_mem (U.inv_mem (U.mul_mem u.property v.property)) (U.mul_mem v.property u.property),by
        change f (((u:H)*(v:H))⁻¹ * ((v:H)*(u:H))) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]⟩
    exact inv_mul_eq_one.mp (mem_bot.mp (hdis.le_bot hk))
  have hpre : IsMulCommutative ((P : Subgroup B).comap f) := by
    let : IsMulCommutative U := hUcomm
    have decomp (a : (P : Subgroup B).comap f) :
        ∃ u : U, ∃ k : f.ker, (a:H) = (u:H)*(k:H) := by
      have ha : f a ∈ U.map f := hU.symm ▸ a.property
      obtain ⟨u,hu,he⟩ := ha
      refine ⟨⟨u,hu⟩,⟨u⁻¹*a,?_⟩,by simp⟩
      simp only [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨u,k,ha⟩ := decomp a
    obtain ⟨v,l,hb⟩ := decomp b
    have huv : (u:H)*(v:H) = (v:H)*(u:H) := congrArg Subtype.val (mul_comm u v)
    have hk (x:H) := mem_center_iff.mp (hc k.property) x
    have hl (x:H) := mem_center_iff.mp (hc l.property) x
    change (a:H)*(b:H)=(b:H)*(a:H)
    rw [ha,hb]
    calc
      (u:H)*k*(v*l) = (u:H)*(k*v)*l := by group
      _ = (u:H)*(v*k)*l := by rw [← hk v]
      _ = ((u:H)*v)*(k*l) := by group
      _ = ((v:H)*u)*(l*k) := by rw [huv,← hk l]
      _ = (v:H)*(u*l)*k := by group
      _ = (v:H)*(l*u)*k := by rw [hl u]
      _ = (v:H)*l*(u*k) := by group
  have hnd := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow_preimage f hf hc P hpre
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (card_eq_one.mp (hp.card_eq_or_dvd.resolve_right hnd))

private theorem kernel_le_action_kernel
    {H B A : Type*} [Group H] [Finite H] [Group B] [Finite B] [Group A]
    {p : ℕ} [Fact p.Prime]
    (f : H →* B) (hf : Function.Surjective f) (hp : IsPGroup p f.ker)
    (ρ : H →* A) (hc : ⁅f.ker,⊤⁆ ≤ ρ.ker)
    (P : Sylow p B) [IsMulCommutative P]
    (U : Subgroup H) (hU : U.map f = P) (hdis : U ⊓ f.ker ≤ ρ.ker)
    (hn : (normalizer (P : Set B)).comap f ≤ normalizer (U : Set H))
    (hcomm : ⁅(P : Subgroup B),normalizer (P : Set B)⁆ = P)
    (j : H) (hgen : U ⊔ U.map (MulAut.conj j).toMonoidHom = ⊤) :
    f.ker ≤ ρ.ker := by
  let K := f.ker ⊓ ρ.ker
  let q := QuotientGroup.mk' K
  let f' := QuotientGroup.lift K f inf_le_left
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hf' : Function.Surjective f' := QuotientGroup.lift_surjective_of_surjective K f hf inf_le_left
  have hk : f'.ker = f.ker.map q := QuotientGroup.ker_lift K f inf_le_left
  have hp' : IsPGroup p f'.ker := hk ▸ hp.map q
  have hc' : f'.ker ≤ center (H ⧸ K) := by
    intro a ha
    obtain ⟨a,rfl⟩ := hq a
    have ha : a ∈ f.ker := ha
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b,rfl⟩ := hq b
    apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨?_,hc (commutator_mem_commutator ha (mem_top b))⟩
    change f ⁅a,b⁆ = 1
    rw [map_commutatorElement,MonoidHom.mem_ker.mp ha]
    simp
  have hU' : (U.map q).map f' = P := by
    rw [map_map,QuotientGroup.lift_comp_mk',hU]
  have hd' : Disjoint (U.map q) f'.ker := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro a ⟨⟨u,hu,rfl⟩,huf⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨huf,hdis ⟨hu,huf⟩⟩
  have hn' : (normalizer (P : Set B)).comap f' ≤ normalizer (U.map q : Set (H ⧸ K)) := by
    intro a ha
    obtain ⟨a,rfl⟩ := hq a
    exact U.le_normalizer_map q (mem_map_of_mem q (hn ha))
  have hgen' : U.map q ⊔ (U.map q).map (MulAut.conj (q j)).toMonoidHom = ⊤ := by
    have he : (MulAut.conj (q j)).toMonoidHom.comp q = q.comp (MulAut.conj j).toMonoidHom := by
      apply MonoidHom.ext
      intro a
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
    rw [map_map,he,← map_map,← Subgroup.map_sup,hgen,map_top_of_surjective q hq]
  have hi := central_kernel_trivial f' hf' hc' hp' P (U.map q) hU' hd' hn' hcomm (q j) hgen'
  intro a ha
  have hqa : q a = 1 := hi (by change f a = f' 1; rw [map_one]; exact ha)
  exact ((QuotientGroup.eq_one_iff a).mp hqa).2


public noncomputable section
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The exact kernel of the marked pair acts trivially on the literal quotient. -/
theorem pairAction_kernel_trivial_on_quotient
    (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hroot : actionImage (V := V) (auxiliaryW E) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ≤ (L ⊔ (T:Subgroup G)).pCoreIn 2) :
    let I := oppositeJoin (auxiliaryW E) (y:G)
    let Q := corePair (auxiliaryW E) (y:G)
    let N := pairDenominator E (y:G)
    let _ := denominator_normal_in_corePair E m y.property hW hPhi
    ∀ (ρ : I →* MulAut (Q ⧸ N.subgroupOf Q)),
      (∀ i : I, ∀ q : Q, ∀ hq : (i:G)*(q:G)*(i:G)⁻¹ ∈ Q,
        ρ i (QuotientGroup.mk' (N.subgroupOf Q) q) =
          QuotientGroup.mk' (N.subgroupOf Q) ⟨(i:G)*(q:G)*(i:G)⁻¹,hq⟩) →
      (pairAction E m hW g y hi).ker ≤ ρ.ker := by
  dsimp only
  intro ρ hρ
  let _ := denominator_normal_in_corePair E m y.property hW hPhi
  let _ := quotient_elementary E m y.property hW hPhi hcore
  let I := oppositeJoin (auxiliaryW E) (y:G)
  let Q := corePair (auxiliaryW E) (y:G)
  let N := pairDenominator E (y:G)
  let f := pairAction E m hW g y hi
  let U := (auxiliaryW E).subgroupOf I
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow E.input.field.Carrier 2
  have hp := source_corePair_properties E m y.property hcore
  have hIQ := (normal_subgroupOf_iff_le_normalizer (hp.1.trans (pCoreIn_le 2 _))).mp hp.2.1
  have hQker : Q.subgroupOf I ≤ ρ.ker := by
    intro i hiQ
    apply MulEquiv.ext
    intro v
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Q) v
    rw [hρ i a (le_normalizer_iff.mp hIQ i i.property a a.property)]
    let b : Q := ⟨i,hiQ⟩
    have he : (⟨(i:G)*(a:G)*(i:G)⁻¹,le_normalizer_iff.mp hIQ i i.property a a.property⟩ : Q) =
        b*a*b⁻¹ := Subtype.ext rfl
    rw [he,map_mul,map_mul,map_inv]
    change _ = QuotientGroup.mk' (N.subgroupOf Q) a
    simp only [mul_comm, mul_assoc, mul_inv_cancel, one_mul]
    rfl
  have hker : f.ker = pCore 2 I := pairAction_ker_eq_core E m hW g y hi
  have hc : ⁅f.ker,⊤⁆ ≤ ρ.ker := by
    apply commutator_le.mpr
    intro a ha b _
    apply hQker
    apply hp.2.2
    exact commutator_mem_commutator (mem_map_of_mem I.subtype (hker ▸ ha)) b.property
  have hd : U ⊓ f.ker ≤ ρ.ker := by
    intro a ha
    apply hQker
    exact mem_sup_left ⟨ha.1,mem_map_of_mem I.subtype (hker ▸ ha.2)⟩
  obtain ⟨j,hj,hjW⟩ := exists_inner_opposite_conjugator E m hW g hpoint y hy hi
  have hjU : U.map (MulAut.conj (⟨j,hj⟩ : I)).toMonoidHom =
      (((auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom).subgroupOf I) := by
    apply map_injective I.subtype_injective
    rw [map_map]
    have he : I.subtype.comp (MulAut.conj (⟨j,hj⟩ : I)).toMonoidHom =
        (MulAut.conj j).toMonoidHom.comp I.subtype := rfl
    rw [he,← map_map,map_subgroupOf_eq_of_le (show auxiliaryW E ≤ I from le_sup_left),
      map_subgroupOf_eq_of_le (show (auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom ≤ I from le_sup_right)]
    exact hjW
  have hg : U ⊔ U.map (MulAut.conj (⟨j,hj⟩ : I)).toMonoidHom = ⊤ := by
    rw [hjU,← subgroupOf_sup (show auxiliaryW E ≤ I from le_sup_left)
      (show (auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom ≤ I from le_sup_right)]
    exact subgroupOf_self I
  let : IsMulCommutative P := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨s,hs⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent E.input.field.Carrier a).mp a.property
    obtain ⟨t,ht⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent E.input.field.Carrier b).mp b.property
    change (a:SL(2,E.input.field.Carrier)) * b = (b:SL(2,E.input.field.Carrier)) * a
    rw [← hs,← ht,← Matrix.SpecialLinearGroup.transvection_add,
      ← Matrix.SpecialLinearGroup.transvection_add,add_comm]
  have hq : 4 ≤ Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    exact (show 4 = 2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) E.input.nonbinary)
  exact kernel_le_action_kernel f (pairAction_surjective E m hW g y hi)
    (hker ▸ pCore_isPGroup) ρ hc P U
    (pairAction_root E m hW g y hi hroot) hd
    (pairAction_normalizer_lifts E m hW g y hi hroot hmove)
    (Matrix.SpecialLinearGroup.commutator_upperUnipotent_rankOneBorel hq) ⟨j,hj⟩ hg

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
