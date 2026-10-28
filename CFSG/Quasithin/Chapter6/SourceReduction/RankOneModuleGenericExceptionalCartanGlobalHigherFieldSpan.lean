module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldParity
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# The actual reduced plus-torus module in the Hermitian Cartan branch

The fixed space of the original Sylow intersection on the Hermitian
omega-span has order 2ˢ. The literal quotient conjugation model shows
that an odd Borel element fixes a nonzero vector precisely when its
(2ˢ+1)-st power is one, including the original two-core kernel.
Consequently the original plus torus of order 2ˢ−1 acts freely on the
nonidentity fixed points. One orbit exhausts the punctured fixed line.

Thus its omega-span is exactly the full Sylow-fixed subgroup and equals
the full Cartan omega-span. The original Cartan and Sylow preserve it.
Sylow inheritance from the central elementary seed proves reducedness in
the literal plus-torus/Sylow join. This establishes the module, size and
invariance premises used in 5.1.6(4). The numerical application of 3.1.6
and selection of the Hermitian model remain separate source obligations.

Source: Aschbacher--Smith 5.1.6(4), printed pp.632--633, and its original
5.2.2 application on p.647, with B.2.13--14, p.78 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
local instance (s : ℕ) : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

private theorem hermitian_sylow_fixed_card (s : ℕ) [NeZero s]
    (S : Sylow 2 SL(2,Field s)) :
    Nat.card (BinaryOffender.fixedSpace (SL2.BinarySmall.hermitian s) S) = 2^s := by
  obtain ⟨a,_,ha,_⟩ := Matrix.SpecialLinearGroup.sylow_odd_subgroup_diagonal_coordinates
    S ⊥ bot_le (by simp)
  rw [Nat.card_congr (BinaryOffender.fixedSpaceConjEquiv (SL2.BinarySmall.hermitian s) S a).toEquiv,
    ha, Nat.card_congr (upperFixedEquiv s).toEquiv,card_fixedField]

variable {G : Type*} [Group G] [Finite G]

private theorem hermitian_fixed_geometry
    {T : Sylow 2 G} {L U : Subgroup G} (s : ℕ) [NeZero s]
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : IsConjugationModel L U (SL2.BinarySmall.hermitian s)) :
    Nat.card (U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) : Subgroup G) = 2^s ∧
    ∀ x ∈ localBorel T L, Odd (orderOf x) →
      ∀ z ∈ U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G), z ≠ 1 →
        (x*z*x⁻¹=z ↔ x^(2^s+1)=1) := by
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let S := P.mapSurjective hq
  let ρ := SL2.BinarySmall.hermitian s
  have hfixed (l : L) (u : U) : ρ (q l) (f u).toAdd = (f u).toAdd ↔
      (l:G)*(u:G)*(l:G)⁻¹ = (u:G) := by
    constructor
    · intro he
      have hh := hf l u
      change (f.symm (Multiplicative.ofAdd (ρ (q l) (f u).toAdd)) : G) = _ at hh
      rw [he] at hh
      change (f.symm (f u) : G) = _ at hh
      rw [f.symm_apply_apply] at hh
      exact hh.symm
    · intro he
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply U.subtype_injective
      change (f.symm (Multiplicative.ofAdd (ρ (q l) (f u).toAdd)) : G) = (f.symm (f u) : G)
      rw [f.symm_apply_apply]
      exact (hf l u).trans he
  have hiff (u : U) : (f u).toAdd ∈ BinaryOffender.fixedSpace ρ S ↔
      (u:G) ∈ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    constructor
    · intro hu l hl
      let lL : L := ⟨l,hl.2⟩
      have hlP : lL ∈ (P : Subgroup L) := by rw [hP]; exact hl.1
      have he := (hfixed lL u).mp (hu ⟨q lL,mem_map_of_mem q hlP⟩)
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hu g
      obtain ⟨l,hl,he⟩ := g.property
      change ρ g.val (f u).toAdd = _
      rw [←he]
      apply (hfixed l u).mpr
      have hlT : (l:G) ∈ (T : Subgroup G) := by
        change l ∈ (P : Subgroup L) at hl
        rwa [hP] at hl
      exact mul_inv_eq_iff_eq_mul.mpr (hu l ⟨hlT,l.property⟩)
  let C := U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)
  let b : C ≃ BinaryOffender.fixedSpace ρ S :=
    { toFun z := ⟨(f ⟨z,z.property.1⟩).toAdd,(hiff _).mpr z.property.2⟩
      invFun v := ⟨f.symm (Multiplicative.ofAdd v.val),
        (f.symm (Multiplicative.ofAdd v.val)).property,
        (hiff _).mp (by simpa only [f.apply_symm_apply,toAdd_ofAdd] using v.property)⟩
      left_inv z := by
        apply Subtype.ext
        change (f.symm (f ⟨z,z.property.1⟩) : G) = (z:G)
        exact congrArg Subtype.val (f.symm_apply_apply _)
      right_inv v := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (f.apply_symm_apply _) }
  refine ⟨(Nat.card_congr b).trans (hermitian_sylow_fixed_card s S),?_⟩
  intro x hx ho z hz hz1
  let xL : L := ⟨x,hx.1⟩
  let zU : U := ⟨z,hz.1⟩
  have hn : q xL ∈ normalizer (S : Set SL(2,Field s)) := by
    have hxN : xL ∈ normalizer (P : Set L) := by
      have hh : x ∈ (normalizer ((T : Subgroup G).subgroupOf L : Set L)).map L.subtype := by
        rwa [←localBorel_eq_map]
      change L.subtype xL ∈ _ at hh
      have hh' := (mem_map_iff_mem L.subtype_injective).mp hh
      change xL ∈ normalizer ((P : Subgroup L) : Set L)
      rw [hP]
      exact hh'
    exact (le_normalizer_map (H := (P : Subgroup L)) q) (mem_map_of_mem q hxN)
  have hoL : Odd (orderOf xL) := by simpa only [← Subgroup.orderOf_coe xL] using ho
  have hoq : Odd (orderOf (q xL)) := hoL.of_dvd_nat (orderOf_map_dvd q xL)
  have hz0 : (f zU).toAdd ≠ 0 := by
    intro he
    exact hz1 (congrArg Subtype.val (f.injective (he.trans f.map_one.symm)))
  have hb := SylowTorus.odd_normalizer_fixed_iff s S (q xL) hn hoq
    (f zU).toAdd ((hiff _).mpr hz.2) hz0
  rw [hfixed] at hb
  refine hb.trans ?_
  constructor
  · intro hp
    have hmem : xL^(2^s+1) ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply e.injective
      change q (xL^(2^s+1)) = e 1
      rw [map_pow,hp,map_one]
    let y : pCore 2 L := ⟨xL^(2^s+1),hmem⟩
    have hyodd : Odd (orderOf y) := by
      rw [Subgroup.orderOf_mk]
      exact hoL.of_dvd_nat (orderOf_pow_dvd _)
    have hy := (pCore_isPGroup (p:=2) (G:=L)).orderOf_coprime hyodd.coprime_two_left y
    have hy1 : y = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hy (dvd_refl _) (dvd_refl _))
    exact congrArg (fun v : pCore 2 L => ((v:L):G)) hy1
  · intro hp
    have hpL : xL^(2^s+1)=1 := Subtype.ext hp
    rw [←map_pow,hpL,map_one]

/-- The original plus-torus orbit fills exactly the Sylow-fixed line in the
Hermitian omega-span. It has binary order 2^s and is invariant under A and T. -/
theorem Input.hermitian_plus_span
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) D
    V = U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    Nat.card V = 2^s ∧
    A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    D ⊓ centralizer (V : Set G) = ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z L
  let V := conjugateSpanBy Z D
  let C := U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)
  obtain ⟨hCc,hfix⟩ := hermitian_fixed_geometry s h.sylow_normalizes hm
  change Nat.card C = 2^s at hCc
  have hZT : Z ≤ (T : Subgroup G) := fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hZC : Z ≤ C := by
    intro z hz
    exact ⟨le_conjugateSpanBy Z L hz,fun t ht =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht.1⟩
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
    have hr := LocalOmega.span_reduced T L (h.qtke.evenCharacteristic T)
      h.maximal_local.1 h.sylow_normalizes
    have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
      h.maximal_local.1 h.sylow_normalizes
    exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (hu.2.trans (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))).mp hr.normal)
  have hTinter : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans inf_normalizer_le_normalizer_inf
  have hnorm : A ⊔ (T : Subgroup G) ≤ normalizer (C : Set G) := by
    apply (le_inf (sup_le ((c.left_le.trans inf_le_left).trans
      (le_normalizer_conjugateSpanBy Z L)) hTU)
      (sup_le (c.left_le.trans inf_le_right) hTinter |>.trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hVC : V ≤ C := conjugateSpanBy_le hZC (hDA.trans (le_sup_left.trans hnorm))
  have hW0 : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hW0 h.reduced_le_sylow
      (le_sup_right.trans (reduced_normalizes h.reduced)))
  have hzZ : (z:G) ∈ Z := by
    let := h.reduced.2.1
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨h.reduced_le_sylow z.property.1,
        elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,z.property.2.2⟩
  have hz0 : (z:G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hodd : Odd (2^s-1) := by
    have hh := (even_two : Even (2:ℕ)).pow_of_ne_zero (NeZero.ne s)
    have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp hh; omega)
  have hcop : (2^s+1).Coprime (2^s-1) := by
    have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
    rw [show 2^s+1 = (2^s-1)+2 by omega,Nat.coprime_self_add_left]
    exact hodd.coprime_two_left
  have hfree (x : G) (hx : x ∈ D) (he : x*(z:G)*x⁻¹=(z:G)) : x=1 := by
    have hd : orderOf x ∣ 2^s-1 := by
      rw [←hDc,←Subgroup.orderOf_mk x hx]
      exact _root_.orderOf_dvd_natCard _
    have hn := (hfix x (c.left_le (hDA hx)) (hodd.of_dvd_nat hd)
      z (hZC hzZ) hz0).mp he
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn) hd)
  let orb : D → V := fun d =>
    ⟨(d:G)*(z:G)*(d:G)⁻¹,subset_closure ⟨d,d.property,z,hzZ,rfl⟩⟩
  have horb0 (d : D) : orb d ≠ 1 := by
    intro he
    apply hz0
    have hh := congrArg Subtype.val he
    change (MulAut.conj (d:G)) (z:G) = 1 at hh
    exact (MulAut.conj (d:G)).map_eq_one_iff.mp hh
  have hi : Function.Injective orb := by
    intro a b he
    have hh : (b:G)*(z:G)*(b:G)⁻¹=(a:G)*(z:G)*(a:G)⁻¹ :=
      (congrArg Subtype.val he).symm
    have hf := hfree ((a:G)⁻¹*(b:G)) (D.mul_mem (D.inv_mem a.property) b.property) (by
      calc
        (a:G)⁻¹*(b:G)*(z:G)*((a:G)⁻¹*(b:G))⁻¹ =
            (a:G)⁻¹*((b:G)*(z:G)*(b:G)⁻¹)*(a:G) := by group
        _ = (z:G) := by rw [hh]; group)
    exact Subtype.ext (inv_mul_eq_one.mp hf)
  let f : Option D → V := fun d => d.elim 1 orb
  have hfi : Function.Injective f := by
    intro a b he
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (horb0 b he.symm).elim
    | some a =>
      cases b with
      | none => exact (horb0 a he).elim
      | some b => exact congrArg some (hi he)
  have hlow := Nat.card_le_card_of_injective f hfi
  have hopt : Nat.card (Option D) = Nat.card D+1 := by
    let : Fintype D := Fintype.ofFinite D
    simp only [Nat.card_eq_fintype_card,Fintype.card_option]
  rw [hopt,hDc] at hlow
  have hp : 0 < (2:ℕ)^s := pow_pos (by decide) _
  have he : V = C := eq_of_le_of_card_ge hVC (by omega)
  change V = C ∧ Nat.card V = 2^s ∧ A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧ _
  refine ⟨he,by rw [he]; exact hCc,by rw [he]; exact hnorm,?_⟩
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply hfree x hx.1
  exact mul_inv_eq_iff_eq_mul.mpr ((hx.2 z (le_conjugateSpanBy Z D hzZ)).symm)

/-- The same plus-torus span is the full Cartan span and is 2-reduced in
the literal plus-torus/Sylow join, as required by source 3.1.5. -/
theorem Input.hermitian_plus_span_reduced
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    conjugateSpanBy Z D = conjugateSpanBy Z A ∧
    conjugateSpanBy Z D ∈ reducedFamily (D ⊔ (T : Subgroup G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let V := conjugateSpanBy Z D
  let J := D ⊔ (T : Subgroup G)
  have hg := h.hermitian_plus_span c s hm hDA hDc
  have hn : J ≤ normalizer (V : Set G) := (sup_le_sup_right hDA _).trans hg.2.2.1
  have hjoin : conjugateSpanBy Z J = V := le_antisymm
    (conjugateSpanBy_le (le_conjugateSpanBy Z D) hn)
    (conjugateSpanBy_mono le_rfl le_sup_left)
  have hZT : Z ≤ (T : Subgroup G) := fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZJ : Z ≤ J := hZT.trans le_sup_right
  have hVJ : V ≤ J := hjoin ▸ conjugateSpanBy_le_self hZJ
  have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  let := hu.1
  have hVU : V ≤ conjugateSpanBy Z L :=
    conjugateSpanBy_mono le_rfl (hDA.trans (c.left_le.trans inf_le_left))
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (inclusion hVU) (inclusion_injective hVU)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hz : omegaOneCenterAmbient (S : Subgroup J) = Z.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hZJ]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hclosure : normalClosure (omegaOneCenterAmbient (S : Subgroup J) : Set J) = V.subgroupOf J := by
    rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ J hZJ,hjoin]
  let : IsElementaryAbelian 2 (V.subgroupOf J) := IsElementaryAbelian.subgroupOf hVJ
  let : IsMulCommutative (normalClosure (omegaOneCenterAmbient (S : Subgroup J) : Set J)) := by
    rw [hclosure]
    infer_instance
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (S : Subgroup J)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hr := isPReduced_normalClosure_of_sylow_central S
    (omegaOneCenterAmbient (S : Subgroup J))
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  rw [hclosure] at hr
  refine ⟨le_antisymm (conjugateSpanBy_mono le_rfl hDA)
    (conjugateSpanBy_le (le_conjugateSpanBy Z D) (le_sup_left.trans hg.2.2.1)),?_⟩
  exact ⟨hVJ,inferInstance,hr.normal,hr.quotient_pCore_eq_bot⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
