module
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PerfectCentralizerLift
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Exponent two for abelian MS commutator cores

Let L be a perfect normal subgroup, R a two-subgroup containing O₂(G),
and G=LR. Assume that the image of L modulo O₂(G) is quasisimple and is
all of F* of that quotient, and that no nontrivial characteristic subgroup
of R is normal in G. Then an abelian [O₂(G),L] is elementary abelian.

MS3 forces an automorphic translate of this commutator core to escape
O₂(G). An involution in its quotient image supplies a quadratic actor.
Its squared action commutes with L, so its commutators with L fix every
square in the core. Component dichotomy and the absence of two-elements
in the quotient's Fitting subgroup force L itself to fix those squares.
The identity [[O₂(G),L],L]=[O₂(G),L] then kills all squares.

This extends the existing binary MS exponent argument to quasisimple
quotients with an odd covering center. In particular it does not replace
SL₃(4) by its projective quotient. Source context: Aschbacher--Smith
C.1.31 and the abelian rows of C.1.34, printed pp.135--137; the argument
adapts the repository's BinaryMS abelian-core exponent proof.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.MSAbelianCommutator
variable {G : Type*} [Group G] [Finite G]
variable (L R : Subgroup G) [L.Normal] [Group.IsPerfect L]
variable (hR : IsPGroup 2 R) (hNR : (pCore 2 G) ≤ R) (hgen : L ⊔ R = ⊤)
  (hms : ∀ C : Subgroup R, C.Characteristic → (C.map R.subtype).Normal → C = ⊥)

omit [L.Normal] in
private theorem twoPerfect : IsPPerfect 2 L := by
  intro A hA hp
  let := hA
  let := hp.isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ A)

omit [L.Normal] in
private theorem idempotent : ⁅(⁅pCore 2 G,L⁆ : Subgroup G),L⁆ = (⁅pCore 2 G,L⁆ : Subgroup G) :=
  commutator_isPPerfect_idempotent L (pCore 2 G) (twoPerfect L) pCore_isPGroup le_normalizer_of_normal

include hNR hgen hms in
omit [Finite G] [L.Normal] [Group.IsPerfect L] in
private theorem exists_automorphic_image (hne : (⁅pCore 2 G,L⁆ : Subgroup G) ≠ ⊥) :
    ∃ a : MulAut R, ¬ ((((⁅pCore 2 G,L⁆ : Subgroup G)).subgroupOf R).map a.toMonoidHom).map R.subtype ≤ (pCore 2 G) := by
  classical
  have hDR : (⁅pCore 2 G,L⁆ : Subgroup G) ≤ R := (commutator_le_left (pCore 2 G) L).trans hNR
  let A := ((⁅pCore 2 G,L⁆ : Subgroup G)).subgroupOf R
  let C : Subgroup R := ⨆ a : MulAut R, A.map a.toMonoidHom
  have hAC : A ≤ C := by
    have hh := le_iSup (fun a : MulAut R => A.map a.toMonoidHom) (MulEquiv.refl R)
    change A.map (MonoidHom.id R) ≤ C at hh
    simpa only [map_id] using hh
  have hchar : C.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro a
    change (⨆ b : MulAut R, A.map b.toMonoidHom).map a.toMonoidHom ≤ C
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro b
    rw [map_map]
    exact le_iSup_of_le (b.trans a) (by rfl)
  by_contra! hall
  have hCN : C.map R.subtype ≤ (pCore 2 G) := by
    change (⨆ a : MulAut R, A.map a.toMonoidHom).map R.subtype ≤ _
    rw [Subgroup.map_iSup]
    exact iSup_le hall
  have hDC : (⁅pCore 2 G,L⁆ : Subgroup G) ≤ C.map R.subtype := by
    rw [← map_subgroupOf_eq_of_le hDR]
    exact map_mono hAC
  have hLC : L ≤ normalizer (C.map R.subtype) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hCN le_rfl).trans hDC
  let : C.Characteristic := hchar
  have hRC : R ≤ normalizer (C.map R.subtype) := by
    have hh := C.le_normalizer_map R.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, R.range_subtype] using hh
  have hn : (C.map R.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hLC hRC
  have hCbot := hms C hchar hn
  apply hne
  exact le_bot_iff.mp (by simpa only [hCbot, Subgroup.map_bot] using hDC)

private def conjugation : G →* MulAut (⁅pCore 2 G,L⁆ : Subgroup G) := MulAut.conjNormal

include hR hNR hgen hms in
omit [Group.IsPerfect L] in
private theorem exists_quadratic_actor (hne : (⁅pCore 2 G,L⁆ : Subgroup G) ≠ ⊥) [IsMulCommutative (⁅pCore 2 G,L⁆ : Subgroup G)] :
    ∃ a : G, a ∈ R ∧ a ∉ (pCore 2 G) ∧ a ^ 2 ∈ (pCore 2 G) ∧
      ∀ d : (⁅pCore 2 G,L⁆ : Subgroup G), conjugation L a (conjugation L a d) * d = (conjugation L a d) ^ 2 := by
  have hDR : (⁅pCore 2 G,L⁆ : Subgroup G) ≤ R := (commutator_le_left (pCore 2 G) L).trans hNR
  obtain ⟨b, hb⟩ := exists_automorphic_image L R hNR hgen hms hne
  let A := (((⁅pCore 2 G,L⁆ : Subgroup G)).subgroupOf R).map b.toMonoidHom
  let X := A.map R.subtype
  let : A.Normal := (inferInstance : (((⁅pCore 2 G,L⁆ : Subgroup G)).subgroupOf R).Normal).map b.toMonoidHom b.surjective
  have hXcomm : IsMulCommutative X := inferInstance
  have hRX : R ≤ normalizer X := by
    have hh := A.le_normalizer_map R.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, R.range_subtype] using hh
  let E := X.map (QuotientGroup.mk' (pCore 2 G))
  have hEne : E ≠ ⊥ := by
    intro he
    apply hb
    simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff X).mp he
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hEne
  have hEp : IsPGroup 2 E := ((hR.to_subgroup A).map R.subtype).map (QuotientGroup.mk' (pCore 2 G))
  obtain ⟨n, hn, hncard⟩ := hEp.nontrivial_iff_card.mp inferInstance
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := E) 2
    (hncard ▸ dvd_pow_self 2 (by omega))
  obtain ⟨a, ha, hae⟩ := e.property
  have haN : a ∉ (pCore 2 G) := by
    intro haN
    have ha1 : (QuotientGroup.mk' (pCore 2 G)) a = 1 := (QuotientGroup.eq_one_iff a).mpr haN
    have he1 : e = 1 := Subtype.ext (hae ▸ ha1)
    simp only [he1, orderOf_one] at he
    omega
  have ha2 : a ^ 2 ∈ (pCore 2 G) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (pCore 2 G)) (a ^ 2) = 1
    rw [map_pow, hae]
    exact congrArg Subtype.val (he ▸ pow_orderOf_eq_one e)
  refine ⟨a, map_subtype_le A ha, haN, ha2, ?_⟩
  intro d
  let f := conjugation L a
  have hXD : ⁅X,(⁅pCore 2 G,L⁆ : Subgroup G)⁆ ≤ X := le_normalizer_iff_commutator_le_left.mp (hDR.trans hRX)
  have hy : ((f d * d⁻¹ : (⁅pCore 2 G,L⁆ : Subgroup G)) : G) ∈ X :=
    hXD (commutator_mem_commutator ha d.property)
  have hfix : f (f d * d⁻¹) = f d * d⁻¹ := by
    apply Subtype.ext
    change a * ((f d * d⁻¹ : (⁅pCore 2 G,L⁆ : Subgroup G)) : G) * a⁻¹ = _
    rw [← (le_centralizer_iff_isMulCommutative.mpr hXcomm) ha _ hy, mul_inv_cancel_right]
  have heq : f (f d) * (f d)⁻¹ = f d * d⁻¹ := by
    simpa only [map_mul, map_inv] using hfix
  change f (f d) * d = (f d) ^ 2
  calc
    f (f d) * d = (f (f d) * (f d)⁻¹) * (f d * d) := by group
    _ = (f d * d⁻¹) * (f d * d) := by rw [heq]
    _ = (f d) ^ 2 := by rw [mul_mul_mul_comm, inv_mul_cancel, mul_one, pow_two]

variable [IsQuasisimple (L.map (QuotientGroup.mk' (pCore 2 G)))]
  (hF : generalizedFitting (G ⧸ (pCore 2 G)) = (L.map (QuotientGroup.mk' (pCore 2 G))))

private theorem normal_image_centralizes (C : Subgroup G) [C.Normal] (hne : ¬ L ≤ C) :
    C.map (QuotientGroup.mk' (pCore 2 G)) ≤ centralizer ((L.map (QuotientGroup.mk' (pCore 2 G))) : Set (G ⧸ (pCore 2 G))) := by
  let : (L.map (QuotientGroup.mk' (pCore 2 G))).Normal := Normal.map inferInstance (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _)
  let : (C.map (QuotientGroup.mk' (pCore 2 G))).Normal := Normal.map inferInstance (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _)
  have hBC : ¬ (L.map (QuotientGroup.mk' (pCore 2 G))) ≤ C.map (QuotientGroup.mk' (pCore 2 G)) := by
    intro hb
    have hLCN : L ≤ C ⊔ (pCore 2 G) := by
      simpa only [comap_map_eq, QuotientGroup.ker_mk'] using map_le_iff_le_comap.mp hb
    let π := QuotientGroup.mk' C
    have himage : L.map π ≤ (pCore 2 G).map π := by
      have hh := map_mono (f := π) hLCN
      simpa only [Subgroup.map_sup, π, QuotientGroup.map_mk'_self, bot_sup_eq] using hh
    have hp : IsPGroup 2 (L.map π) := (pCore_isPGroup.map π).to_le himage
    let f := π.subgroupMap L
    have hf : f = 1 := (twoPerfect L).hom_eq_one_of_isPGroup hp f
    apply hne
    intro l hl
    apply (QuotientGroup.eq_one_iff (N := C) l).mp
    exact congrArg Subtype.val (DFunLike.congr_fun hf ⟨l,hl⟩)
  have hz := (IsComponent.normal_dichotomy
    (⟨(inferInstance : (L.map (QuotientGroup.mk' (pCore 2 G))).Normal).isSubnormal,inferInstance⟩ : IsComponent _ (L.map (QuotientGroup.mk' (pCore 2 G))))
      (C.map (QuotientGroup.mk' (pCore 2 G)))).resolve_left hBC
  rw [commutator_comm] at hz
  exact commutator_eq_bot_iff_le_centralizer.mp hz

include hR hF in
omit [Group.IsPerfect L] [IsQuasisimple (L.map (QuotientGroup.mk' (pCore 2 G)))] in
private theorem radical_image_centralizer : R.map (QuotientGroup.mk' (pCore 2 G)) ⊓ centralizer ((L.map (QuotientGroup.mk' (pCore 2 G))) : Set (G ⧸ (pCore 2 G))) = ⊥ := by
  let : (L.map (QuotientGroup.mk' (pCore 2 G))).Normal := Normal.map inferInstance (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _)
  let C := centralizer ((L.map (QuotientGroup.mk' (pCore 2 G))) : Set (G ⧸ (pCore 2 G)))
  have hCB : C ≤ (L.map (QuotientGroup.mk' (pCore 2 G))) := by
    simpa only [hF] using centralizer_generalizedFitting_le (G ⧸ pCore 2 G)
  let : IsMulCommutative C := ⟨⟨fun a b => Subtype.ext (a.property b (hCB b.property)).symm⟩⟩
  have hCF : C ≤ fittingSubgroup (G ⧸ (pCore 2 G)) := le_sSup ⟨inferInstance,inferInstance⟩
  let A := R.map (QuotientGroup.mk' (pCore 2 G)) ⊓ C
  have hp : IsPGroup 2 A := (hR.map (QuotientGroup.mk' (pCore 2 G))).to_le inf_le_left
  have hAO : A ≤ pPrimeCore 2 (G ⧸ (pCore 2 G)) := inf_le_right.trans
    (hCF.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 (pCore_quotient_pCore_eq_bot 2)))
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hc : Nat.Coprime (Nat.card A) (Nat.card (pPrimeCore 2 (G ⧸ (pCore 2 G)))) := by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G ⧸ (pCore 2 G))).pow_left n
  exact bot_unique ((le_inf le_rfl hAO).trans (disjoint_of_coprime_natCard hc).le_bot)

include hR hF in
private theorem component_le_of_radical_commutator (C : Subgroup G) [C.Normal]
    (a : G) (ha : a ∈ R) (hane : a ∉ (pCore 2 G)) (hcomm : ⁅zpowers a,L⁆ ≤ C) : L ≤ C := by
  by_contra hLC
  have himage : ⁅(zpowers a).map (QuotientGroup.mk' (pCore 2 G)),(L.map (QuotientGroup.mk' (pCore 2 G)))⁆ ≤ C.map (QuotientGroup.mk' (pCore 2 G)) := by
    rw [← map_commutator]
    exact map_mono hcomm
  have hz : ⁅⁅(zpowers a).map (QuotientGroup.mk' (pCore 2 G)),(L.map (QuotientGroup.mk' (pCore 2 G)))⁆,(L.map (QuotientGroup.mk' (pCore 2 G)))⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (himage.trans (normal_image_centralizes L C hLC))
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_iterated_eq_bot _ (L.map (QuotientGroup.mk' (pCore 2 G))) hz)
  have he : (QuotientGroup.mk' (pCore 2 G)) a = 1 := (radical_image_centralizer L R hR hF).le
    ⟨mem_map_of_mem (QuotientGroup.mk' (pCore 2 G)) ha,hc (mem_map_of_mem (QuotientGroup.mk' (pCore 2 G)) (mem_zpowers a))⟩
  exact hane ((QuotientGroup.eq_one_iff a).mp he)


omit [IsQuasisimple (L.map (QuotientGroup.mk' (pCore 2 G)))] in
private theorem elementary_of_fixed_squares [IsMulCommutative (⁅pCore 2 G,L⁆ : Subgroup G)]
    (hsq : ∀ x ∈ (⁅pCore 2 G,L⁆ : Subgroup G), x ^ 2 ∈ centralizer (L : Set G)) : IsElementaryAbelian 2 (⁅pCore 2 G,L⁆ : Subgroup G) := by
  let C : Subgroup G := ((powMonoidHom 2 : (⁅pCore 2 G,L⁆ : Subgroup G) →* (⁅pCore 2 G,L⁆ : Subgroup G)).ker).map ((⁅pCore 2 G,L⁆ : Subgroup G)).subtype
  have hDC : (⁅pCore 2 G,L⁆ : Subgroup G) ≤ C := by
    rw [← idempotent L]
    apply commutator_le.mpr
    intro x hx l hl
    have hm : ⁅x,l⁆ ∈ (⁅pCore 2 G,L⁆ : Subgroup G) := commutator_le_left (⁅pCore 2 G,L⁆ : Subgroup G) L (commutator_mem_commutator hx hl)
    have hc : x * ⁅x,l⁆ = ⁅x,l⁆ * x :=
      congrArg Subtype.val (mul_comm (⟨x,hx⟩ : (⁅pCore 2 G,L⁆ : Subgroup G)) ⟨⁅x,l⁆,hm⟩)
    have hh : ⁅x^2,l⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hsq x hx) l hl).symm
    have hp : ⁅x,l⁆ ^ 2 = 1 := by
      rwa [pow_two, commutatorElement_mul_left_eq_conj_mul, hc,
        mul_inv_cancel_right, ← pow_two] at hh
    exact ⟨⟨⁅x,l⁆,hm⟩, Subtype.ext hp, rfl⟩
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨y,hy,he⟩ := hDC x.property
  exact (show y = x from Subtype.ext he) ▸ hy

include hR hNR hgen hms hF in
/-- If a perfect normal subgroup has the full quasisimple generalized Fitting
image modulo O₂(G), the MS characteristic condition forces its abelian core
commutator to have exponent two. A possible odd covering center is retained. -/
theorem elementary_of_abelian [IsMulCommutative (⁅pCore 2 G,L⁆ : Subgroup G)] : IsElementaryAbelian 2 (⁅pCore 2 G,L⁆ : Subgroup G) := by
  by_cases hne : (⁅pCore 2 G,L⁆ : Subgroup G) = ⊥
  · rw [hne]
    exact {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun _ => Subsingleton.elim _ _) }
  obtain ⟨a,ha,haN,ha2,hquad⟩ := exists_quadratic_actor L R hR hNR hgen hms hne
  let S := (powMonoidHom 2 : (⁅pCore 2 G,L⁆ : Subgroup G) →* (⁅pCore 2 G,L⁆ : Subgroup G)).range
  let : S.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    rintro f x ⟨y,rfl⟩
    exact ⟨f y,(map_pow f y 2).symm⟩
  let X := S.map ((⁅pCore 2 G,L⁆ : Subgroup G)).subtype
  let : X.Normal := ConjAct.normal_of_characteristic_of_normal
  let C := centralizer (X : Set G)
  let : C.Normal := inferInstance
  have himage : ⁅(pCore 2 G).map (conjugation L), L.map (conjugation L)⁆ = ⊥ := by
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro d hd
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change d * (x : G) * d⁻¹ = x
    rw [← (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative (⁅pCore 2 G,L⁆ : Subgroup G))) hd x x.property, mul_inv_cancel_right]
  have hcomm (l : L) : ⁅a,(l : G)⁆ ∈ C := by
    let f := conjugation L a
    let g := conjugation L l
    have hfg (v : (⁅pCore 2 G,L⁆ : Subgroup G)) : f (f (g v)) = g (f (f v)) := by
      have hh := (commutator_eq_bot_iff_le_centralizer.mp himage)
        (mem_map_of_mem (conjugation L) ha2) _
        (mem_map_of_mem (conjugation L) l.property)
      have he := congrArg (fun k : MulAut (⁅pCore 2 G,L⁆ : Subgroup G) => k v) hh.symm
      simpa only [map_pow, pow_two, map_mul, MulAut.mul_apply] using he
    have hfgsq (v : (⁅pCore 2 G,L⁆ : Subgroup G)) : (f (g v)) ^ 2 = (g (f v)) ^ 2 := by
      calc
        (f (g v)) ^ 2 = f (f (g v)) * g v := (hquad (g v)).symm
        _ = g (f (f v)) * g v := by rw [hfg]
        _ = g (f (f v) * v) := (map_mul g _ _).symm
        _ = g ((f v) ^ 2) := by rw [hquad]
        _ = (g (f v)) ^ 2 := map_pow g _ _
    rintro x ⟨d,⟨y,hy⟩,rfl⟩
    subst d
    have he := hfgsq (f.symm (g.symm y))
    simp only [MulEquiv.apply_symm_apply] at he
    change ((f * g * f⁻¹ * g⁻¹) y) ^ 2 = y ^ 2 at he
    rw [← map_pow] at he
    have hh : conjugation L ⁅a,(l : G)⁆ (y ^ 2) = y ^ 2 := by
      simpa only [commutatorElement_def,map_mul,map_inv] using he
    have hv := congrArg Subtype.val hh
    change ⁅a,(l : G)⁆ * ((y : G) ^ 2) * ⁅a,(l : G)⁆⁻¹ = (y : G) ^ 2 at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have hcomm' : ⁅zpowers a,L⁆ ≤ C := by
    let π := QuotientGroup.mk' C
    rw [← QuotientGroup.ker_mk' C]
    apply (Subgroup.map_eq_bot_iff _ (f := π)).mp
    rw [map_commutator]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply map_le_iff_le_comap.mpr
    apply zpowers_le.mpr
    rintro x ⟨l,hl,rfl⟩
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm ⟨l,hl⟩)
  have hLC := component_le_of_radical_commutator L R hR hF C a ha haN hcomm'
  apply elementary_of_fixed_squares L
  intro d hd l hl
  exact (hLC hl _ (mem_map_of_mem ((⁅pCore 2 G,L⁆ : Subgroup G)).subtype
    (show (⟨d,hd⟩ : (⁅pCore 2 G,L⁆ : Subgroup G)) ^ 2 ∈ S from ⟨⟨d,hd⟩,rfl⟩))).symm

end Theory.GroupTheory.MSAbelianCommutator
