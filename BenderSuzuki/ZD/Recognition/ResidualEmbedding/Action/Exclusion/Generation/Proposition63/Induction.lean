module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.Proposition63.Foundations
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalBasic
public import BenderSuzuki.SE.Borel
public import BenderSuzuki.SE.Lemma312

/-!
# Proper-subgroup induction in distinguished Proposition 6.3

Minimality is applied only in the eligible proper distinguished closure.
The full ZD conclusion supplies its Borel quotient. Strong embedding removes
the central square-one factor, and the normal Sylow two-subgroup of the Borel
contains the image of each distinguished generator of `M°`. The two-residual
`O²(M°)` therefore maps trivially into this quotient.

Source: GLS, Volume 4, Chapter 2, Proposition 6.3 and [II4; 3.2(b)],
`refs/KGroup/GLS4/Chapter2.tex`, lines 997–1007.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem prop63_structure_bender
    {F : Type u} [Group F] [Finite F] {W : Set F} {M : Subgroup F}
    (hstr : StructureConclusion W M)
    (hs : IsStronglyEmbedded (M.comap (Subgroup.closure W).subtype)) :
    let C := Subgroup.closure W
    let Y := M.comap C.subtype
    let N := pPrimeCore 2 C
    let q := QuotientGroup.mk' N
    IsSimpleBenderGroup (C ⧸ N) ∧ N ≤ Y ∧ IsBorelSubgroup (Y.map q) := by
  let C := Subgroup.closure W
  let Y := M.comap C.subtype
  let N := pPrimeCore 2 C
  let q := QuotientGroup.mk' N
  let Q := C ⧸ N
  let X := commutator Q
  obtain ⟨u, huY, hu2, hgen, hgenQ, _, hcomm, hmodel, hN, hBorel, _⟩ := hstr
  change u ∈ Y at huY
  change commutator C ⊔ Subgroup.zpowers u = ⊤ at hgen
  change X ⊔ Subgroup.zpowers (q u) = ⊤ at hgenQ
  change ∀ x ∈ X, ∀ v ∈ Subgroup.zpowers (q u), Commute x v at hcomm
  change IsSimpleBenderGroup X at hmodel
  change N ≤ Y ⊓ commutator C at hN
  change IsBorelSubgroup (((Y ⊓ commutator C).map q).subgroupOf X) at hBorel
  have hodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsQ := hs.map_quotient_of_odd_kernel (hN.trans inf_le_left) hodd
  have hc : q u ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro a
    have hle : X ⊔ Subgroup.zpowers (q u) ≤ Subgroup.centralizer ({q u} : Set Q) := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm x hx (q u) (Subgroup.mem_zpowers _)).eq) ?_
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    rw [hgenQ] at hle
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top a))
  have hqu : q u = 1 := by
    by_contra hqu
    have hqi : PFAppendixIII.IsInvolution (q u) := ⟨hqu, by rw [← map_pow, hu2, map_one]⟩
    apply hsQ.ne_top
    apply top_unique
    intro a _
    exact hsQ.centralizer_le (Subgroup.mem_map_of_mem q huY) hqi
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hc a))
  have hu : u = 1 := by
    by_contra hu
    exact (IsInvolution.quotient_mk_of_odd_kernel N hodd ⟨hu, hu2⟩).ne_one hqu
  have hperfect : commutator C = ⊤ := by simpa only [hu, Subgroup.zpowers_one_eq_bot, sup_bot_eq] using hgen
  have hX : X = ⊤ := by simpa only [hqu, Subgroup.zpowers_one_eq_bot, sup_bot_eq] using hgenQ
  let e : X ≃* Q :=
    { toFun := fun x => x
      invFun := fun x => ⟨x, hX ▸ Subgroup.mem_top x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hB : (((Y ⊓ commutator C).map q).subgroupOf X).map e.toMonoidHom = Y.map q := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, heq⟩ := hx
      exact ⟨y, hy.1, heq⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨q y, hX ▸ Subgroup.mem_top _⟩, ?_, rfl⟩
      exact ⟨y, ⟨hy, hperfect ▸ Subgroup.mem_top y⟩, rfl⟩
  exact ⟨hmodel.map_mulEquiv e, hN.trans inf_le_left, hB ▸ hBorel.map_mulEquiv e⟩
private theorem sq_eq_one_mem_normal_sylow_two
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (hPnormal : (P : Subgroup G).Normal)
    {x : G} (hx : x ^ 2 = 1) : x ∈ (P : Subgroup G) := by
  by_cases hxone : x = 1
  · simp [hxone]
  · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have horder : orderOf x = 2 := orderOf_eq_prime hx hxone
    have hzp : IsPGroup 2 (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1)
      simp [Nat.card_zpowers, horder]
    obtain ⟨Q, hzpQ⟩ := hzp.exists_le_sylow
    let : Unique (Sylow 2 G) := Sylow.unique_of_normal P hPnormal
    have hQP : Q = P := Subsingleton.elim _ _
    rw [hQP] at hzpQ
    exact hzpQ (Subgroup.mem_zpowers x)

/-- The induction step puts `O²(M°)` in the odd core of proper `L`. -/
public theorem prop63_residual_le_oddCore
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hs : ActionSectionThree Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) :
    (prop63Residual Z M).map M.subtype ≤
      (twoPrimeCore (residualGenerated M z t)).map
        (residualGenerated M z t).subtype := by
  let L := residualGenerated M z t
  let C := Subgroup.closure (L.subtype ⁻¹' Z)
  let A := prop63Core Z M
  let ML := M.comap L.subtype
  let N := pPrimeCore 2 C
  let q := QuotientGroup.mk' N
  let B := (ML.comap C.subtype).map q
  have hAL : A.map M.subtype ≤ L := by
    rw [prop63Core_map]
    exact prop63_distinguishedClosure_le_residualGenerated h.disconnected hs hz hzM ht htM
  have htL : t ∈ L :=
    (show Subgroup.zpowers t ≤ L from le_sup_right.trans le_sup_left) (Subgroup.mem_zpowers t)
  have hzL : z ∈ L :=
    (show Subgroup.zpowers z ≤ L from le_sup_left.trans le_sup_left) (Subgroup.mem_zpowers z)
  have heligible : ¬ L ≤ M := fun he => htM (he htL)
  have hnonempty : ∃ z ∈ Z, z ∈ L ∧ z ∈ M := ⟨z, hz, hzL, hzM⟩
  have hCtop : C = ⊤ := residualGenerated_localClosure_eq_top h.disconnected hz ht
  let e : C ≃* L := (MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv
  have he_apply (c : C) : e c = (c : L) := rfl
  have hCstrong : IsStronglyEmbedded (ML.comap C.subtype) :=
    r.local_embedding L hL heligible hnonempty
  have hrL : TwoRankAtLeastTwo L := by
    have hr := localIntersection_twoRank_of_distinguishedClosure_le h r L
      (prop63_distinguishedClosure_le_residualGenerated h.disconnected hs hz hzM ht htM)
    exact hr.map_of_injective ML.subtype ML.subtype_injective
  have hrC : TwoRankAtLeastTwo C := hrL.map_of_injective e.symm.toMonoidHom e.symm.injective
  have hstr : StructureConclusion (L.subtype ⁻¹' Z) ML :=
    (h.conclusion_subgroup L hL heligible hnonempty).resolve_left (not_not.mpr hrC)
  obtain ⟨hmodel, _, hB⟩ := prop63_structure_bender hstr hCstrong
  obtain ⟨P, hPnormal, _⟩ := simpleBender_borel_normalSylow_regular hB hmodel
  let PB := (P : Subgroup B).map B.subtype
  let fL : A →* L := {
    toFun a := ⟨((a : M) : G), hAL (Subgroup.mem_map_of_mem M.subtype a.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let fC : A →* C := e.symm.toMonoidHom.comp fL
  let f : A →* C ⧸ N := q.comp fC
  have hfB (a : A) : f a ∈ B := by
    refine Subgroup.mem_map.mpr ⟨fC a, ?_, rfl⟩
    change (((fC a : C) : L) : G) ∈ M
    have he : ((fC a : C) : L) = fL a := e.apply_symm_apply (fL a)
    rw [he]
    exact (a : M).property
  have hfPB (a : A) : f a ∈ PB := by
    have ha : (a : M) ∈ Subgroup.closure (M.subtype ⁻¹' Z) := a.property
    let D := PB.comap f
    have hclosed : A ≤ (D.map A.subtype) := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      let a : A := ⟨x, Subgroup.subset_closure hx⟩
      let b : B := ⟨f a, hfB a⟩
      have ha2 : a ^ 2 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact (h.disconnected.involutions x hx).sq_eq_one
      have hb2 : b ^ 2 = 1 := by
        apply Subtype.ext
        change f a ^ 2 = 1
        rw [← map_pow, ha2, map_one]
      have hbP := sq_eq_one_mem_normal_sylow_two P hPnormal hb2
      exact ⟨a, Subgroup.mem_map.mpr ⟨b, hbP, rfl⟩, rfl⟩
    obtain ⟨a', ha', he⟩ := hclosed a.property
    have hea : a' = a := Subtype.ext he
    exact hea ▸ ha'
  have himage : IsPGroup 2 f.range := by
    apply (P.isPGroup'.map B.subtype).to_le
    rintro x ⟨a, rfl⟩
    exact hfPB a
  let fr := f.rangeRestrict
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : External.hallPResidual 2 A ≤ fr.ker :=
    External.hallPResidual_le_ker_of_isPGroup fr himage
  have hNmap : N.map e.toMonoidHom = twoPrimeCore L :=
    pPrimeCore_map_iso (p := 2) e
  rintro y ⟨ym, hym, rfl⟩
  obtain ⟨a, ha, he⟩ := hym
  have hfone : f a = 1 := congrArg Subtype.val (hker ha : fr a = 1)
  have haN : fC a ∈ N := (QuotientGroup.eq_one_iff (N := N) (fC a)).mp hfone
  have hfLN : fL a ∈ twoPrimeCore L := by
    rw [← hNmap]
    exact ⟨fC a, haN, e.apply_symm_apply (fL a)⟩
  exact ⟨fL a, hfLN, congrArg Subtype.val he⟩

end BenderSuzuki.ZD
