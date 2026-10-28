module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SylowStructure
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# The elementary eight forces fusion inside the quaternion subgroup

Both local Sylow two-subgroups have order 64 and are ambient Sylow
subgroups. Conjugate a Sylow of M into a chosen Sylow of H, carrying the
actual F*(M) with it. The central involution z of H centralizes that
conjugate elementary eight. Self-centralization in M then puts z in it.
The full action of M fuses all its nonidentity points to z.

This elementary eight meets the normal quaternion subgroup Q₁Q₂ in at
least four points: its relative index divides both 8 and 18. Thus z has
a conjugate inside Q₁Q₂ outside its center. The aligned whole subgroups have intersection of order 192, of index three
in H and seven in the conjugate of M. The construction uses precisely
(G1)–(G2) and no simplicity, weak-closure or prescribed fusion assumption.
It supplies the inside-product fusion premise used in Fong–Wong §2F,
Nagoya Math. J. 36 (1969), pp.153–154, DOI 10.1017/S0027763000013180,
for Aschbacher–Smith I.4.5, printed p.417.

The extension and ambient recognition remain with `qt-i45-g2-recognition`;
`Chapter14Sylow.lean` applies these conclusions to the source local data.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.V_normal V_elementary

theorem M_sylow_card (T : Sylow 2 c.M) : Nat.card T = 64 := by
  have hd : Nat.card T ∣ 1344 := by
    simpa only [M_card c] using (T : Subgroup c.M).card_subgroup_dvd_card
  have hl : 64 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card
    (show 2^6 ∣ Nat.card c.M by rw [M_card c]; decide)
  have hc : Nat.Coprime (Nat.card T) 21 := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 21).pow_left n
  exact Nat.dvd_antisymm (hc.dvd_of_dvd_mul_right hd) hl

theorem M_sylow_is_ambient (T : Sylow 2 c.M) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = (T : Subgroup c.M).map c.M.subtype := by
  obtain ⟨S, hS⟩ := (T.isPGroup'.map c.M.subtype).exists_le_sylow
  refine ⟨S, (eq_of_le_of_card_ge hS ?_).symm⟩
  rw [card_map_of_injective c.M.subtype_injective, M_sylow_card c T, ambient_sylow_card c S]

/-- Align M's elementary eight inside any chosen H-Sylow. Every nonidentity
point of this actual conjugate is ambient-conjugate to the marked involution. -/
theorem exists_seed_in_H_sylow (T : Sylow 2 c.H) (z : c.H)
    (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup c.H))
    (hH : c.H = centralizer ({(z : G)} : Set G)) :
    ∃ E : Subgroup c.H, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ E ≤ T ∧ z ∈ E ∧
      (∃ g : G,
        E.map c.H.subtype = (c.V.map c.M.subtype).map (MulAut.conj g).toMonoidHom ∧
        (T : Subgroup c.H).map c.H.subtype ≤ c.M.map (MulAut.conj g).toMonoidHom ∧
        Nat.card (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom : Subgroup G) = 192) ∧
      ∀ x : E, x ≠ 1 → IsConj (z : G) ((x : c.H) : G) := by
  let U : Sylow 2 c.M := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := M_sylow_is_ambient c U
  obtain ⟨S, hS⟩ := H_sylow_is_ambient c T
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  let a : G ≃* G := MulAut.conj g
  let f : c.M →* G := a.toMonoidHom.comp c.M.subtype
  have hf : Function.Injective f := a.injective.comp c.M.subtype_injective
  have hUS : (U : Subgroup c.M).map f = (S : Subgroup G) := by
    rw [show (U : Subgroup c.M).map f =
      ((U : Subgroup c.M).map c.M.subtype).map a.toMonoidHom from (map_map _ _ _).symm,
      ← hR]
    exact congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  have hV : c.V ≤ U := (IsElementaryAbelian.isPGroup 2 c.V).le_sylow_of_normal U
  have hES : c.V.map f ≤ (S : Subgroup G) := hUS ▸ map_mono hV
  have hEH : c.V.map f ≤ c.H := hES.trans (hS ▸ map_subtype_le _)
  have hzS : (z : G) ∈ (S : Subgroup G) := hS ▸ mem_map_of_mem c.H.subtype hzT
  have hzU : (z : G) ∈ (U : Subgroup c.M).map f := hUS ▸ hzS
  obtain ⟨u, hu, huf⟩ := hzU
  have huV : u ∈ c.V := by
    rw [← V_centralizer c]
    intro v hv
    apply hf
    simp only [map_mul]
    have hvH : f v ∈ c.H := hEH (mem_map_of_mem f hv)
    have he := mem_centralizer_singleton_iff.mp (hH ▸ hvH)
    simpa only [huf] using he
  let E := (c.V.map f).subgroupOf c.H
  let e : E ≃* c.V := (subgroupOfEquivOfLe hEH).trans (c.V.equivMapOfInjective f hf).symm
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hET : E ≤ T := by
    intro x hx
    have hxS := hES hx
    rw [hS] at hxS
    obtain ⟨y, hy, he⟩ := hxS
    have hexy : y = x := Subtype.ext he
    exact hexy ▸ hy
  have hune : (⟨u, huV⟩ : c.V) ≠ 1 := by
    intro he
    have huz : (z : G) = 1 := by rw [← huf, show u = 1 from congrArg Subtype.val he, map_one]
    have hz1 : z = 1 := Subtype.ext huz
    simp [hz1] at hz
  have hCM : (centralizer ({u} : Set c.M)).map f =
      c.H ⊓ c.M.map a.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      constructor
      · have hv' := congrArg f (mem_centralizer_singleton_iff.mp hv)
        simp only [map_mul,huf] at hv'
        exact hH.symm ▸ mem_centralizer_singleton_iff.mpr hv'
      · exact mem_map_of_mem a.toMonoidHom v.property
    · rintro ⟨hxH,v,hv,hvx⟩
      refine ⟨⟨v,hv⟩, ?_, hvx⟩
      apply mem_centralizer_singleton_iff.mpr
      apply hf
      simp only [map_mul,huf]
      have hvf : f ⟨v,hv⟩ = x := hvx
      rw [hvf]
      exact mem_centralizer_singleton_iff.mp (hH ▸ hxH)
  have hCMcard : Nat.card (c.H ⊓ c.M.map a.toMonoidHom : Subgroup G) = 192 := by
    rw [← hCM, card_map_of_injective hf]
    exact seed_point_centralizer_card c ⟨u,huV⟩ hune
  refine ⟨E, inferInstance, (Nat.card_congr e.toEquiv).trans (V_card c), hET,
    ⟨u, huV, huf⟩, ⟨g, ?_, ?_, hCMcard⟩, ?_⟩
  · exact (map_subgroupOf_eq_of_le hEH).trans (map_map _ _ _).symm
  · rw [← hS, ← hUS]
    rintro x ⟨v,hv,rfl⟩
    exact mem_map_of_mem a.toMonoidHom v.property
  · intro x hx
    obtain ⟨v, hv, hvf⟩ := x.property
    have hvne : (⟨v, hv⟩ : c.V) ≠ 1 := by
      intro he
      apply hx
      apply Subtype.ext
      apply Subtype.ext
      have hvf' : f v = ((x : c.H) : G) := hvf
      exact hvf'.symm.trans (by rw [show v = 1 from congrArg Subtype.val he, map_one]; rfl)
    obtain ⟨m, hm⟩ := seed_nonidentity_conjugate c ⟨u,huV⟩ ⟨v,hv⟩ hune hvne
    have hh : IsConj (f u) (f v) := f.map_isConj (isConj_iff.mpr ⟨m,hm⟩)
    rw [huf, hvf] at hh
    exact hh

/-- The actual local pair can be aligned over any prescribed Sylow of H.
The overlap has indices three and seven, and contains that original Sylow. -/
theorem exists_local_pair (T : Sylow 2 c.H) :
    ∃ g : G,
      (T : Subgroup c.H).map c.H.subtype ≤ c.M.map (MulAut.conj g).toMonoidHom ∧
      Nat.card (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom : Subgroup G) = 192 ∧
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).relIndex c.H = 3 ∧
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom).relIndex
        (c.M.map (MulAut.conj g).toMonoidHom) = 7 := by
  obtain ⟨z,hz,hgen,hH⟩ := exists_marked_involution c
  have hzQ : z ∈ quaternionCore c := by
    have hzline : z ∈ c.H₁ ⊓ c.H₂ := hgen ▸ mem_zpowers z
    rw [← quaternionCore_center c] at hzline
    exact map_subtype_le _ hzline
  obtain ⟨E,_,_,_,_,⟨g,_,hTM,hcard⟩,_⟩ := exists_seed_in_H_sylow c T z hz
    (quaternionCore_le_sylow c T hzQ) hH
  refine ⟨g,hTM,hcard,?_,?_⟩
  · have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom) c.H bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hcard,H_card c] at hi
    omega
  · have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
      (c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom)
      (c.M.map (MulAut.conj g).toMonoidHom) bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,hcard,
      card_map_of_injective (MulAut.conj g).injective,M_card c] at hi
    omega

/-- The transported elementary eight meets the normal quaternion subgroup in
at least a four-group; its nonidentity points remain in one ambient class. -/
theorem exists_fused_four_in_quaternionCore :
    ∃ (z : c.H) (A : Subgroup c.H),
      orderOf z = 2 ∧ c.H = centralizer ({(z : G)} : Set G) ∧
      zpowers z = c.H₁ ⊓ c.H₂ ∧ A ≤ quaternionCore c ∧
      IsElementaryAbelian 2 A ∧ 4 ≤ Nat.card A ∧ z ∈ A ∧
      ∀ x : A, x ≠ 1 → IsConj (z : G) ((x : c.H) : G) := by
  obtain ⟨z, hz, hgen, hH⟩ := exists_marked_involution c
  let T : Sylow 2 c.H := Classical.choice inferInstance
  have hzQ : z ∈ quaternionCore c := by
    have hzline : z ∈ c.H₁ ⊓ c.H₂ := hgen ▸ mem_zpowers z
    rw [← quaternionCore_center c] at hzline
    exact map_subtype_le _ hzline
  obtain ⟨E, he, hc, hET, hzE, _, hf⟩ := exists_seed_in_H_sylow c T z hz
    (quaternionCore_le_sylow c T hzQ) hH
  let Q := quaternionCore c
  let A := Q ⊓ E
  let := he
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion (show A ≤ E from inf_le_right)) (inclusion_injective _)
  have hi : Q.relIndex E ≤ 2 := by
    have h18 : Q.relIndex E ∣ 18 := by
      exact (Q.relIndex_dvd_index_of_normal E).trans (quaternionCore_index c ▸ dvd_rfl)
    have h8 : Q.relIndex E ∣ 8 := by simpa only [hc] using Q.relIndex_dvd_card E
    have hd : Q.relIndex E ∣ 2 := by
      simpa only [show Nat.gcd 18 8 = 2 from rfl] using Nat.dvd_gcd h18 h8
    exact Nat.le_of_dvd (by decide) hd
  have hcard : 4 ≤ Nat.card A := by
    have hh := (Q.subgroupOf E).card_mul_index
    have hce : Nat.card (Q.subgroupOf E) = Nat.card A := by
      rw [← card_map_of_injective E.subtype_injective, subgroupOf_map_subtype]
    change Nat.card (Q.subgroupOf E) * Q.relIndex E = Nat.card E at hh
    rw [hce, hc] at hh
    nlinarith
  refine ⟨z, A, hz, hH, hgen, inf_le_left, inferInstance, hcard, ⟨hzQ,hzE⟩, ?_⟩
  intro x hx
  apply hf ⟨x,x.property.2⟩
  intro heq
  apply hx
  apply Subtype.ext
  exact congrArg (fun y : E => (y : c.H)) heq

/-- The central involution fuses into Q₁Q₂ away from its center. This uses
(G2), bypassing the outside-involution alternative in Fong–Wong §2F. -/
theorem exists_distinguished_fusion_in_quaternionCore :
    ∃ (z : G) (t : quaternionCore c), orderOf z = 2 ∧
      c.H = centralizer ({z} : Set G) ∧ orderOf t = 2 ∧
      t ∉ center (quaternionCore c) ∧ IsConj z ((t : c.H) : G) := by
  obtain ⟨z,A,hz,hH,hgen,hAQ,he,hcard,hzA,hf⟩ := exists_fused_four_in_quaternionCore c
  have hnot : ¬ A ≤ c.H₁ ⊓ c.H₂ := by
    intro h
    have hh := card_le_of_le h
    rw [intersection_card c] at hh
    omega
  obtain ⟨t,htA,htZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have htne : (⟨t,htA⟩ : A) ≠ 1 := by
    intro h
    apply htZ
    have ht1 : t = 1 := congrArg (fun y : A => (y : c.H)) h
    rw [ht1]
    exact (c.H₁ ⊓ c.H₂).one_mem
  have htconj := hf ⟨t,htA⟩ htne
  have hzG : orderOf (z:G) = 2 := (orderOf_coe z).trans hz
  have htG : orderOf (t:G) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp htconj
    exact (congrArg orderOf hg).symm.trans ((MulAut.conj g).orderOf_eq _ |>.trans hzG)
  refine ⟨z, ⟨t,hAQ htA⟩, hzG, hH, ?_, ?_, htconj⟩
  · rw [orderOf_mk, ← orderOf_coe t]
    exact htG
  · intro h
    apply htZ
    rw [← quaternionCore_center c]
    exact mem_map_of_mem (quaternionCore c).subtype h

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
