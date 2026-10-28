module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCentralizerBound
public import Theory.SpecificGroups.AlternatingFiveInvolutionCover

/-!
# The natural layer is the local two-core

The canonical conjugate elementary eight meets Q=O₂(LT) in the central
line. Its sign kernel therefore contains a square-one element with
nontrivial image in the marked A₅. Modulo V, Q centralizes the perfect
image of L. Correcting the chosen element by its Q factor supplies an
involution in this perfect central two-cover of A₅. The central-cover
involution theorem makes the covering kernel trivial, so L∩Q=V and
O₂(L)=V. No splitting of M or L is assumed.

Source: Aschbacher–Smith, proof of 6.2.13, printed p.687, final paragraph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

private theorem cover_kernel_eq
    {J : Type*} [Group J] [Finite J]
    (L Q V : Subgroup J) [Q.Normal] [V.Normal] [Group.IsPerfect L]
    [IsElementaryAbelian 2 Q]
    (hVL : V ≤ L) (hVQ : V ≤ Q) (hcomm : ⁅Q,L⁆ ≤ V)
    (f : J →* Equiv.Perm (Fin 5)) (hker : f.ker = Q)
    (himage : L.map f = alternatingGroup (Fin 5))
    (a : J) (ha : a ∈ L ⊔ Q) (ha2 : a ^ 2 = 1) (haQ : a ∉ Q) :
    L ⊓ Q = V := by
  let π := QuotientGroup.mk' V
  let B := L.map π
  let F := QuotientGroup.lift V f (hVQ.trans_eq hker.symm)
  let b : L →* B := (π.comp L.subtype).codRestrict B
    (fun x => mem_map_of_mem π x.property)
  have hb : Function.Surjective b := by
    rintro ⟨x,y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective hb
  let g : B →* alternatingGroup (Fin 5) := (F.comp B.subtype).codRestrict _ (by
    rintro ⟨x,y,hy,rfl⟩
    change f y ∈ alternatingGroup (Fin 5)
    rw [← himage]
    exact mem_map_of_mem f hy)
  have hg : Function.Surjective g := by
    rintro ⟨y,hy⟩
    rw [← himage] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact ⟨⟨π x,mem_map_of_mem π hx⟩,rfl⟩
  have hπcomm (q l : J) (hq : q ∈ Q) (hl : l ∈ L) :
      Commute (π q) (π l) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm (commutator_mem_commutator hq hl))
  have hcentral : g.ker ≤ center B := by
    rintro ⟨x,l,hl,rfl⟩ hx
    have hlQ : l ∈ Q := by
      rw [← hker]
      exact congrArg Subtype.val hx
    rw [mem_center_iff]
    rintro ⟨y,k,hk,rfl⟩
    exact Subtype.ext (hπcomm l k hlQ hk).symm.eq
  let : IsElementaryAbelian 2 (Q.map π) := IsElementaryAbelian.map π
  have hp : IsPGroup 2 g.ker := by
    let j : g.ker →* Q.map π := (B.subtype.comp g.ker.subtype).codRestrict _ (by
      rintro ⟨⟨x,l,hl,rfl⟩,hx⟩
      apply mem_map_of_mem π
      rw [← hker]
      exact congrArg Subtype.val hx)
    exact (IsElementaryAbelian.isPGroup 2 (Q.map π)).of_injective j (by
      intro x y h
      exact Subtype.ext (Subtype.ext
        (congrArg (fun t : Q.map π => (t : J ⧸ V)) h)))
  obtain ⟨l,hl,q,hq,he⟩ := mem_sup_of_normal_right.mp ha
  have he' : π l * π q = π a := by rw [← map_mul,he]
  have hq2 : π q ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian q hq, map_one]
  have hl2 : π l ^ 2 = 1 := by
    have hh := congrArg π ha2
    rw [map_pow,map_one,←he',(hπcomm q l hq hl).symm.mul_pow,hq2,mul_one] at hh
    exact hh
  have hlne : g ⟨π l,mem_map_of_mem π hl⟩ ≠ 1 := by
    intro hh
    have hlQ : l ∈ Q := by rw [← hker]; exact congrArg Subtype.val hh
    exact haQ (he ▸ Q.mul_mem hlQ hq)
  have hi := alternatingGroup.injective_of_central_two_kernel_of_involution
    g hg hcentral hp ⟨π l,mem_map_of_mem π hl⟩ (Subtype.ext hl2) hlne
  apply le_antisymm
  · intro x hx
    have hzero : g ⟨π x,mem_map_of_mem π hx.1⟩ = 1 := by
      apply Subtype.ext
      change x ∈ f.ker
      rw [hker]
      exact hx.2
    have heq : π x = 1 := congrArg Subtype.val (hi (hzero.trans g.map_one.symm))
    exact (QuotientGroup.eq_one_iff x).mp heq
  · exact le_inf hVL hVQ


open Subgroup Theory.GroupTheory
open scoped Pointwise
noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The conjugate natural eight meets the local core in the marked central line. -/
theorem LocalAnalysis.equality_conjugate_eight
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      E ≤ (equalityCore L R z).map (centralizer ({z} : Set G)).subtype ∧
      E ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = zpowers z := by
  let H := centralizer ({z} : Set G)
  let P := (equalityCore L R z).map H.subtype
  let V := layer L R
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  obtain ⟨g,hg,_,_,_,_,hi⟩ := hp.pair
  let c := (MulAut.conj g).toMonoidHom
  have hPn : H ≤ normalizer (P : Set G) := by
    have hh := (equalityCore L R z).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hPm : P.map c = P := (mem_normalizer_iff_map_conj_eq).mp (hPn hg)
  let E := (V ⊓ P).map c
  have hE : E = V.map c ⊓ P := by
    change (V ⊓ P).map c = _
    rw [map_inf _ _ _ (MulAut.conj g).injective,hPm]
  let : IsElementaryAbelian 2 V := h611.layer_elementary
  let : IsElementaryAbelian 2 (V ⊓ P : Subgroup G) := IsElementaryAbelian.of_injective
    (inclusion (show V ⊓ P ≤ V from inf_le_left)) (inclusion_injective _)
  have hc : Nat.card E = 8 := by
    rw [Nat.card_congr ((V ⊓ P).equivMapOfInjective c (MulAut.conj g).injective).toEquiv.symm]
    rw [equality_layer_inf_core h611 hz]
    exact A.layer_core_card
  have hEP : E ≤ P := hE ▸ inf_le_right
  refine ⟨E,IsElementaryAbelian.map c,hc,hEP,?_⟩
  have hPQ := A.equality_core_inf_local_core h611 hnatural hz horder hTH hbranch
  change P ⊓ Q = V ⊓ P at hPQ
  have hEQ : E ⊓ Q = E ⊓ V := by
    calc
      E ⊓ Q = E ⊓ (P ⊓ Q) := by rw [←inf_assoc,inf_eq_left.mpr hEP]
      _ = E ⊓ (V ⊓ P) := by rw [hPQ]
      _ = E ⊓ V := by rw [inf_left_comm,inf_eq_left.mpr hEP,inf_comm]
  rw [hEQ,hE,inf_right_comm,inf_comm (V.map c) V]
  change (layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom) ⊓ P = _
  rw [hi,hp.core_center,map_subgroupOf_eq_of_le (zpowers_le.mpr (by
    exact mem_centralizer_singleton_iff.mpr rfl))]
  exact inf_eq_left.mpr ((zpowers_le.mpr hz).trans (by
    have hh := map_mono (f := H.subtype) hp.plane_le_core
    rwa [map_subgroupOf_eq_of_le (h611.ZS_le_T.trans hTH)] at hh))

/-- The conjugate elementary eight supplies a square-one element with
nontrivial even image under the literal marked local quotient. -/
theorem LocalAnalysis.equality_inner_involution
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (f : M →* Equiv.Perm (Fin 5))
    (hker : f.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M) :
    ∃ a : M, a ^ 2 = 1 ∧ f a ∈ alternatingGroup (Fin 5) ∧ f a ≠ 1 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨E,hE,h8,hEP,hEQ⟩ :=
    A.equality_conjugate_eight h611 hnatural hz horder hTH hbranch
  let := hE
  have hEM : E ≤ M := hEP.trans ((equalityCore_le_sylow hTH).trans h611.sylow_le)
  let j : E →* M := inclusion hEM
  let F := f.comp j
  have hk : F.ker = Q.subgroupOf E := by
    ext x
    change j x ∈ f.ker ↔ _
    rw [hker]
    rfl
  have h2 : Nat.card F.ker = 2 := by
    rw [hk, ← inf_subgroupOf_right Q E, Nat.card_congr (subgroupOfEquivOfLe (show Q ⊓ E ≤ E from inf_le_right)).toEquiv]
    rw [inf_comm Q E,hEQ,Nat.card_zpowers,horder]
  let s := Equiv.Perm.sign.comp F
  have hr : Nat.card s.range ≤ 2 := by
    have hh := Nat.card_le_card_of_injective s.range.subtype s.range.subtype_injective
    have hcard : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
    exact hh.trans_eq hcard
  have hex : ∃ x : E, s x = 1 ∧ F x ≠ 1 := by
    by_contra! hno
    have hs : s.ker = F.ker := by
      apply le_antisymm
      · exact fun x hx => hno x hx
      · intro x hx
        change Equiv.Perm.sign (F x) = 1
        rw [show F x = 1 from hx,map_one]
    have hc := s.ker.card_mul_index
    rw [index_ker,hs,h2,h8] at hc
    omega
  obtain ⟨x,hx,hne⟩ := hex
  refine ⟨j x,?_,?_,hne⟩
  · rw [←map_pow,show x ^ 2 = 1 from Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property),map_one]
  · exact Equiv.Perm.mem_alternatingGroup.mpr hx

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The natural layer is the actual two-core of L. -/
theorem LocalAnalysis.equality_layer_eq_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    layer L R = L.pCoreIn 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let V := layer L R
  have hVL : V ≤ L := h611.layer_le_L
  have hVQ : V ≤ Q := h611.layer_le_V.trans (reduced_le_core h611.V_mem)
  have hQM : Q ≤ M := (pCoreIn_le 2 _).trans (sup_le h611.L_le h611.sylow_le)
  let := A.equality_local_core_normal h611 hnatural hz horder hTH hbranch
  let := A.equality_layer_normal h611 hnatural hz horder hTH hbranch
  let : IsElementaryAbelian 2 Q :=
    A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  let : IsElementaryAbelian 2 (Q.subgroupOf M) := IsElementaryAbelian.subgroupOf hQM
  have hB : (L.subgroupOf M).IsCComponent := by
    rw [A.equality_maximal_eq_local h611 hnatural hz horder hTH hbranch]
    exact h611.local_mem.1.prop.1
  let := hB.perfect
  obtain ⟨f,_,hker,himage,_⟩ :=
    A.equality_core_permutation_image h611 hnatural hz horder hTH hbranch
  obtain ⟨a,ha2,haeven,hane⟩ :=
    A.equality_inner_involution h611 hnatural hz horder hTH hbranch f hker
  have ha : a ∈ L.subgroupOf M ⊔ Q.subgroupOf M := by
    rw [←hker,←comap_map_eq,himage]
    exact haeven
  have haQ : a ∉ Q.subgroupOf M := by
    rw [←hker]
    exact hane
  have hcomm : ⁅Q.subgroupOf M,L.subgroupOf M⁆ ≤ V.subgroupOf M := by
    rw [←map_le_map_iff_of_injective M.subtype_injective, map_commutator,
      map_subgroupOf_eq_of_le hQM, map_subgroupOf_eq_of_le h611.L_le,
      map_subgroupOf_eq_of_le (hVL.trans h611.L_le)]
    exact (A.equality_local_core_commutator h611 hnatural hz horder hTH hbranch).le
  have he := cover_kernel_eq (L.subgroupOf M) (Q.subgroupOf M) (V.subgroupOf M)
    (subgroupOf_mono M hVL) (subgroupOf_mono M hVQ) hcomm f hker himage a ha ha2 haQ
  have hLQ : L ⊓ Q = V := by
    have hh := congrArg (Subgroup.map M.subtype) he
    rwa [map_inf _ _ _ M.subtype_injective, map_subgroupOf_eq_of_le h611.L_le,
      map_subgroupOf_eq_of_le hQM, map_subgroupOf_eq_of_le (hVL.trans h611.L_le)] at hh
  have hML : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal
  have hcoreQ : L.pCoreIn 2 ≤ Q := by
    change L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [A.equality_local_core_eq_maximal_core h611 hnatural hz horder hTH hbranch]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans h611.L_le)
      (hML.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  apply le_antisymm
  · have hLV : L ≤ normalizer (V : Set G) :=
      h611.L_le.trans (A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch)
    let : IsElementaryAbelian 2 V := h611.layer_elementary
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVL hLV
  · exact (le_inf (pCoreIn_le 2 L) hcoreQ).trans_eq hLQ

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
