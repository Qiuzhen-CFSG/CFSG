module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.CentralizerQuotient

/-!
# Exponent two for an abelian binary MS commutator core

Write N = O₂(J) and D = [N,L], and assume D is abelian. If every
Aut(R)-translate of D were contained in N, their join would be characteristic
in R and normalized by L: it contains D and [N,L] = D. The genuine MS3
condition excludes this nontrivial normal subgroup of J. Thus an abelian
normal subgroup A of R, isomorphic to D, has nontrivial image modulo N.
Choose a in A with aN of order two. Since [D,A] lies in A, conjugation f by a
is quadratic on D, in the multiplicative form f²(d)d = f(d)².

The action of a² commutes with that of L, because [N,L] = D is abelian.
The quadratic identity therefore makes f commute with L on the squares
of D. Centerlessness of the component quotient supplies a commutator [a,l]
outside N that centralizes those squares. The centralizer of their normal
subgroup either lies in N or contains L, by simplicity of L/O₂(L) and
perfectness of L. Hence L fixes every square; [D,L] = D then kills them.

This proves the abelian exponent assertion required by the binary cases of
Aschbacher--Smith C.1.34, combined manuscript (1 March 2004), pp.136--137,
from the actual MS hypotheses of C.1.31, p.135. The argument is local and
does not invoke the MS93 classification, a natural quotient, or an
identification of D with the central omega module.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)
include h

/-- MS3 forces an automorphic translate of D in R to escape the ambient core. -/
private theorem exists_core_automorphic_image :
    ∃ a : MulAut R, ¬ (((commutatorCore L).subgroupOf R).map a.toMonoidHom).map
      R.subtype ≤ pCore 2 J := by
  classical
  let D := commutatorCore L
  have hDN : D ≤ pCore 2 J :=
    h.commutatorCore_le.trans (h.componentCore_eq_inf.le.trans inf_le_left)
  have hDR : D ≤ R := hDN.trans h.radical.twoCore_le
  let B := D.subgroupOf R
  let K : Subgroup R := ⨆ a : MulAut R, B.map a.toMonoidHom
  have hBK : B ≤ K := by
    have hh := le_iSup (fun a : MulAut R => B.map a.toMonoidHom) (MulEquiv.refl R)
    change B.map (MonoidHom.id R) ≤ K at hh
    simpa only [map_id] using hh
  have hchar : K.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro a
    change (⨆ b : MulAut R, B.map b.toMonoidHom).map a.toMonoidHom ≤ K
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro b
    rw [map_map]
    exact le_iSup_of_le (b.trans a) (by rfl)
  by_contra! hall
  have hKN : K.map R.subtype ≤ pCore 2 J := by
    change (⨆ a : MulAut R, B.map a.toMonoidHom).map R.subtype ≤ _
    rw [Subgroup.map_iSup]
    exact iSup_le hall
  have hDK : D ≤ K.map R.subtype := by
    rw [← map_subgroupOf_eq_of_le hDR]
    exact map_mono hBK
  have hLK : L ≤ normalizer (K.map R.subtype) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hKN le_rfl).trans hDK
  let : K.Characteristic := hchar
  have hRK : R ≤ normalizer (K.map R.subtype) := by
    have hh := K.le_normalizer_map R.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, R.range_subtype] using hh
  have hn : (K.map R.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← h.sup_eq_top]
    exact sup_le hLK hRK
  have hKbot := h.characteristic.eq_bot_of_normal K hn
  apply h.commutatorCore_ne_bot
  exact le_bot_iff.mp (by simpa only [hKbot, Subgroup.map_bot] using hDK)

/-- A normal subgroup has either a small centralizer or trivial component action. -/
private theorem normal_centralizer_dichotomy (K : Subgroup J) [K.Normal] :
    centralizer (K : Set J) ≤ pCore 2 J ∨ L ≤ centralizer (K : Set J) := by
  let := h.component_normal
  let C := centralizer (K : Set J)
  let CL := C.subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    (h.quotientEquiv.trans Matrix.PSL3Two.equiv).isSimpleGroup
  have hnorm : (CL.map q).Normal :=
    (inferInstance : CL.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hnorm.eq_bot_or_eq_top with hc | hc
  · left
    have hCL : C ⊓ L ≤ pCore 2 J := by
      intro x hx
      have hxL : (⟨x,hx.2⟩ : L) ∈ pCore 2 L := by
        have hle := (Subgroup.map_eq_bot_iff CL).mp hc
        simpa only [q, QuotientGroup.ker_mk'] using hle hx.1
      exact (h.componentCore_eq_inf.le (mem_map_of_mem L.subtype hxL)).1
    have hk : ⁅C,L⁆ ≤ h.quotientAction.ker := by
      rw [h.quotientAction_kernel]
      exact (commutator_le_inf C L).trans hCL
    have hi : L.map h.quotientAction = MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
      apply le_antisymm
      · rintro a ⟨l, hl, rfl⟩
        exact ⟨QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩,
          (h.quotientAction_component ⟨l,hl⟩).symm⟩
      · rintro a ⟨x,rfl⟩
        obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
        exact ⟨l,l.property,h.quotientAction_component l⟩
    have hcomm : ⁅C.map h.quotientAction, MulAut.innerSubgroup (L ⧸ pCore 2 L)⁆ = ⊥ := by
      rw [← hi, ← map_commutator]
      exact (Subgroup.map_eq_bot_iff _).mpr hk
    have hzero : C.map h.quotientAction = ⊥ := by
      apply le_bot_iff.mp
      exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (MulAut.centralizer_innerSubgroup_eq_bot h.quotient_center).le
    have hle := (Subgroup.map_eq_bot_iff C).mp hzero
    rwa [h.quotientAction_kernel] at hle
  · right
    have hsup : CL ⊔ pCore 2 L = ⊤ := by
      have hh := congrArg (fun H => H.comap q) hc
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
    have hp : IsPGroup 2 (L ⧸ CL) :=
      isPGroup_quotient_of_sup_eq_top CL (pCore 2 L) pCore_isPGroup hsup
    let := h.component.perfect
    have hs : Subsingleton (L ⧸ CL) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ CL) hp.isNilpotent
    have htop : CL = ⊤ := by
      apply eq_top_iff.mpr
      intro l _
      exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)
    exact subgroupOf_eq_top.mp htop


/-- The escaping abelian normal subgroup supplies a quadratic actor whose
nontrivial quotient image is an involution. The lift need not be an involution. -/
private theorem exists_abelian_quadratic_actor
    (hc : IsMulCommutative (commutatorCore L)) :
    ∃ a : J, a ∉ pCore 2 J ∧ a ^ 2 ∈ pCore 2 J ∧
      ∀ d : commutatorCore L,
        h.coreAmbientConjugation a (h.coreAmbientConjugation a d) * d =
          (h.coreAmbientConjugation a d) ^ 2 := by
  let := hc
  let := h.component_normal
  have hDN : commutatorCore L ≤ pCore 2 J :=
    h.commutatorCore_le.trans (h.componentCore_eq_inf.le.trans inf_le_left)
  have hDR := hDN.trans h.radical.twoCore_le
  obtain ⟨b, hb⟩ := exists_core_automorphic_image h
  let B := ((commutatorCore L).subgroupOf R).map b.toMonoidHom
  let A := B.map R.subtype
  let : B.Normal := (inferInstance : ((commutatorCore L).subgroupOf R).Normal).map
    b.toMonoidHom b.surjective
  have hAcomm : IsMulCommutative A := inferInstance
  have hRA : R ≤ normalizer A := by
    have hh := B.le_normalizer_map R.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, R.range_subtype] using hh
  let q := QuotientGroup.mk' (pCore 2 J)
  let E := A.map q
  have hEne : E ≠ ⊥ := by
    intro he
    apply hb
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff A).mp he
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hEne
  have hEp : IsPGroup 2 E := (h.radical.isPGroup.to_subgroup B).map R.subtype |>.map q
  obtain ⟨n, hn, hncard⟩ := hEp.nontrivial_iff_card.mp inferInstance
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := E) 2
    (hncard ▸ dvd_pow_self 2 (by omega))
  obtain ⟨a, ha, hae⟩ := e.property
  have haN : a ∉ pCore 2 J := by
    intro haN
    have ha1 : q a = 1 := (QuotientGroup.eq_one_iff a).mpr haN
    have he1 : e = 1 := Subtype.ext (hae ▸ ha1)
    simp only [he1, orderOf_one] at he
    omega
  have ha2 : a ^ 2 ∈ pCore 2 J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a ^ 2) = 1
    rw [map_pow, hae]
    exact congrArg Subtype.val (he ▸ pow_orderOf_eq_one e)
  refine ⟨a, haN, ha2, ?_⟩
  intro d
  let f := h.coreAmbientConjugation a
  have hAD : ⁅A, commutatorCore L⁆ ≤ A :=
    le_normalizer_iff_commutator_le_left.mp (hDR.trans hRA)
  have hy : ((f d * d⁻¹ : commutatorCore L) : J) ∈ A := by
    change (h.coreAmbientConjugation a d : J) * (d : J)⁻¹ ∈ A
    rw [h.coreAmbientConjugation_apply]
    exact hAD (commutator_mem_commutator ha d.property)
  have hfix : f (f d * d⁻¹) = f d * d⁻¹ := by
    apply Subtype.ext
    change (h.coreAmbientConjugation a (f d * d⁻¹) : J) = _
    rw [h.coreAmbientConjugation_apply,
      ← (le_centralizer_iff_isMulCommutative.mpr hAcomm) ha _ hy,
      mul_inv_cancel_right]
  have heq : f (f d) * (f d)⁻¹ = f d * d⁻¹ := by
    simpa only [map_mul, map_inv] using hfix
  change f (f d) * d = (f d) ^ 2
  calc
    f (f d) * d = (f (f d) * (f d)⁻¹) * (f d * d) := by group
    _ = (f d * d⁻¹) * (f d * d) := by rw [heq]
    _ = (f d) ^ 2 := by rw [mul_mul_mul_comm, inv_mul_cancel, mul_one, pow_two]

/-- Centerlessness detects an external actor by a component commutator. -/
private theorem exists_component_commutator_outside_core (a : J) (ha : a ∉ pCore 2 J) :
    ∃ l : L, ⁅a,(l : J)⁆ ∉ pCore 2 J := by
  by_contra! hall
  apply ha
  rw [← h.quotientAction_kernel]
  apply (MulAut.centralizer_innerSubgroup_eq_bot h.quotient_center).le
  rintro x ⟨y,rfl⟩
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
  rw [← h.quotientAction_component]
  apply Eq.symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  change ⁅a,(l : J)⁆ ∈ h.quotientAction.ker
  rw [h.quotientAction_kernel]
  exact hall l

/-- One external element fixing all squares forces the component to fix them. -/
private theorem elementary_of_external_square_centralizer
    (hc : IsMulCommutative (commutatorCore L))
    (a : J) (ha : a ∉ pCore 2 J)
    (hfix : ∀ d : commutatorCore L,
      h.coreAmbientConjugation a (d ^ 2) = d ^ 2) :
    IsElementaryAbelian 2 (commutatorCore L) := by
  let := hc
  let := h.component_normal
  let S := (powMonoidHom 2 : commutatorCore L →* commutatorCore L).range
  let : S.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    rintro f x ⟨y,rfl⟩
    exact ⟨f y, (map_pow f y 2).symm⟩
  let K := S.map (commutatorCore L).subtype
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  have haC : a ∈ centralizer (K : Set J) := by
    rintro x ⟨d, ⟨y,hy⟩, rfl⟩
    subst d
    have he := congrArg Subtype.val (hfix y)
    rw [h.coreAmbientConjugation_apply] at he
    change a * ((y : J) ^ 2) * a⁻¹ = (y : J) ^ 2 at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rcases normal_centralizer_dichotomy h K with hle | hle
  · exact (ha (hle haC)).elim
  · apply h.abelianCore_elementary_of_fixed_squares hc
    intro d hd l hl
    exact (hle hl _ (mem_map_of_mem (commutatorCore L).subtype
      (show (⟨d,hd⟩ : commutatorCore L) ^ 2 ∈ S from ⟨⟨d,hd⟩,rfl⟩))).symm

/-- The quadratic identity transfers centrality of the squared action to
commutation on squares; a component commutator then detects exponent two. -/
private theorem elementary_of_quadratic_actor
    (hc : IsMulCommutative (commutatorCore L))
    (a : J) (ha : a ∉ pCore 2 J) (ha2 : a ^ 2 ∈ pCore 2 J)
    (hquad : ∀ d : commutatorCore L,
      h.coreAmbientConjugation a (h.coreAmbientConjugation a d) * d =
        (h.coreAmbientConjugation a d) ^ 2) :
    IsElementaryAbelian 2 (commutatorCore L) := by
  let := hc
  obtain ⟨l,hl⟩ := exists_component_commutator_outside_core h a ha
  apply elementary_of_external_square_centralizer h hc ⁅a,(l : J)⁆ hl
  intro d
  let f := h.coreAmbientConjugation a
  let g := h.coreAmbientConjugation l
  have hfg (v : commutatorCore L) : f (f (g v)) = g (f (f v)) := by
    have hh := (commutator_eq_bot_iff_le_centralizer.mp
      (h.abelianCore_ambient_image_commutator hc))
      (mem_map_of_mem h.coreAmbientConjugation ha2) _
      (mem_map_of_mem h.coreAmbientConjugation l.property)
    have he := congrArg (fun k : MulAut (commutatorCore L) => k v) hh.symm
    simpa only [map_pow, pow_two, map_mul, MulAut.mul_apply] using he
  have hfgsq (v : commutatorCore L) : (f (g v)) ^ 2 = (g (f v)) ^ 2 := by
    calc
      (f (g v)) ^ 2 = f (f (g v)) * g v := (hquad (g v)).symm
      _ = g (f (f v)) * g v := by rw [hfg]
      _ = g (f (f v) * v) := (map_mul g _ _).symm
      _ = g ((f v) ^ 2) := by rw [hquad]
      _ = (g (f v)) ^ 2 := map_pow g _ _
  have he := hfgsq (f.symm (g.symm d))
  simp only [MulEquiv.apply_symm_apply] at he
  change ((f * g * f⁻¹ * g⁻¹) d) ^ 2 = d ^ 2 at he
  rw [← map_pow] at he
  simpa only [commutatorElement_def, map_mul, map_inv] using he

/-- The whole abelian commutator core of a binary MS input has exponent two.
No elementary-core or natural-module premise is required. -/
theorem Input.abelianCore_elementary (hc : IsMulCommutative (commutatorCore L)) :
    IsElementaryAbelian 2 (commutatorCore L) := by
  obtain ⟨a,ha,ha2,hquad⟩ := exists_abelian_quadratic_actor h hc
  exact elementary_of_quadratic_actor h hc a ha ha2 hquad

end CFSG.Quasithin.ChapterC.BinaryMS
