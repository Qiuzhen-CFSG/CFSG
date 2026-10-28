module

public import Theory.GroupTheory.Gaschutz
public import Theory.Frattini.NormalImage
public import Theory.Frattini.NilpotentProducts

/-!
# Odd Frattini subgroups inside normal subgroups of index two

More generally, if N is normal, contains Φ(G), and its index is coprime to
|Φ(G)|, then Φ(G) lies in the ambient image of Φ(N). Modulo that image,
Φ(G) is abelian: its own commutator lies in its own Frattini subgroup,
whose normal image lies in Φ(N). The image of N is Frattini-free.

A minimal supplement shows that an abelian normal subgroup disjoint from
the Frattini subgroup has a complement. Gaschütz lifts this complement
from the image of N, contradicting Frattini nongeneration unless the
remaining image of Φ(G) is trivial. The quotient-map adapter records the
literal maps used for H/O₂(H) and the image of O²(H).

Source: Aschbacher–Smith B.6.8(7) and B.6.10, printed pp.114–117;
Gaschütz's coprime-index complement theorem.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace FrattiniCoprime
variable {G : Type*} [Group G] [Finite G]

/-- An abelian normal subgroup avoiding the Frattini subgroup splits. -/
theorem exists_complement_of_disjoint_frattini (A : Subgroup G) [A.Normal]
    [IsMulCommutative A] (hd : Disjoint A (frattini G)) :
    ∃ M : Subgroup G, A.IsComplement' M := by
  classical
  obtain ⟨M,hM⟩ := exists_minimal_of_wellFoundedLT
    (fun M : Subgroup G => A ⊔ M = ⊤) ⟨⊤,sup_top_eq A⟩
  let B := A ⊓ M
  have hAB : A ≤ normalizer (B : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro a ha
    apply mem_centralizer_iff.mpr
    intro b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hb.1⟩ : A) ⟨a,ha⟩)
  have hMB : M ≤ normalizer (B : Set G) :=
    (le_inf le_normalizer_of_normal M.le_normalizer).trans inf_normalizer_le_normalizer_inf
  let : B.Normal := normalizer_eq_top_iff.mp
    (top_unique (hM.1 ▸ sup_le hAB hMB))
  have hBF : B ≤ frattini G := by
    simp only [frattini,Order.radical,le_iInf_iff]
    intro K hK
    by_contra hBK
    have hgen : K ⊔ B = ⊤ := hK.2 _ (lt_of_le_of_ne le_sup_left
      (fun he => hBK (le_sup_right.trans_eq he.symm)))
    have hMK : M ≤ A ⊔ (K ⊓ M) := by
      intro x hx
      obtain ⟨k,hk,b,hb,hkb⟩ := mem_sup_of_normal_right.mp
        (show x ∈ K ⊔ B from hgen ▸ mem_top x)
      have hkM : k ∈ M := by
        have he : k = x*b⁻¹ := by rw [← hkb]; group
        rw [he]
        exact M.mul_mem hx (M.inv_mem hb.2)
      rw [← hkb]
      exact (A ⊔ (K ⊓ M)).mul_mem (mem_sup_right ⟨hk,hkM⟩) (mem_sup_left hb.1)
    have hAK : A ⊔ (K ⊓ M) = ⊤ := top_unique (hM.1 ▸ sup_le le_sup_left hMK)
    have hMK' : M ≤ K ⊓ M := hM.2 hAK inf_le_right
    exact hBK (inf_le_right.trans (hMK'.trans inf_le_left))
  have hdis : Disjoint A M := disjoint_iff_inf_le.mpr
    ((le_inf inf_le_left hBF).trans hd.le_bot)
  refine ⟨M,isComplement'_of_disjoint_and_mul_eq_univ hdis ?_⟩
  apply Set.eq_univ_iff_forall.mpr
  intro x
  exact mem_sup_of_normal_left.mp (show x ∈ A ⊔ M from hM.1 ▸ mem_top x)

variable {H : Type*} [Group H]

omit [Finite G] in
theorem comap_frattini_of_surjective (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ frattini G) : (frattini H).comap f = frattini G := by
  apply le_antisymm _ (frattini_le_comap_frattini_of_surjective hf)
  intro x hx
  simp only [frattini,Order.radical,mem_iInf]
  intro M hM
  have hker : f.ker ≤ M := hk.trans (frattini_le_coatom hM)
  have hc : IsCoatom (M.map f) := by
    refine ⟨?_,?_⟩
    · intro he
      have hh := congrArg (Subgroup.comap f) he
      rw [comap_map_eq,sup_eq_left.mpr hker,comap_top] at hh
      exact hM.1 hh
    · intro K hK
      have hlt : M < K.comap f := by
        apply lt_of_le_of_ne (map_le_iff_le_comap.mp hK.le)
        intro he
        have hh := congrArg (Subgroup.map f) he
        rw [map_comap_eq_self_of_surjective hf] at hh
        exact hK.ne hh
      have hh := congrArg (Subgroup.map f) (hM.2 _ hlt)
      simpa only [map_comap_eq_self_of_surjective hf,map_top_of_surjective f hf] using hh
  have hfx := frattini_le_coatom hc hx
  have : x ∈ (M.map f).comap f := hfx
  simpa only [comap_map_eq,sup_eq_left.mpr hker] using this

end FrattiniCoprime

namespace FrattiniCoprime
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem frattini_eq_bot_of_ker_eq {H : Type*} [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker = frattini G) :
    frattini H = ⊥ := by
  apply Subgroup.comap_injective hf
  rw [comap_frattini_of_surjective f hf hk.le]
  exact hk.symm

/-- Coprime index transfers the ambient Frattini subgroup into the normal subgroup’s Frattini image. -/
theorem frattini_le_image_of_coprime_index (N : Subgroup G) [N.Normal]
    (hFN : frattini G ≤ N) (hcop : (Nat.card (frattini G)).Coprime N.index) :
    frattini G ≤ (frattini N).map N.subtype := by
  let F := frattini G
  let K := (frattini N).map N.subtype
  let : K.Normal := inferInstance
  have hKN : K ≤ N := map_subtype_le _
  let q := QuotientGroup.mk' K
  have hq := QuotientGroup.mk'_surjective K
  let A := F.map q
  let D := N.map q
  let : A.Normal := (inferInstance : F.Normal).map q hq
  have hAD : A ≤ D := map_mono hFN
  let i : F →* N := inclusion hFN
  let : i.range.Normal := by
    dsimp [i]
    rw [inclusion_range]
    infer_instance
  have hiphi : (frattini F).map i ≤ frattini N := frattini_map_le_of_normal_range i
  let : Group.IsNilpotent F := frattini_nilpotent
  let : IsMulCommutative A := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    obtain ⟨x,hx,hxa⟩ := a.property
    obtain ⟨y,hy,hyb⟩ := b.property
    change (a : G ⧸ K) * b = (b : G ⧸ K) * a
    rw [← hxa,← hyb]
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    let u : F := ⟨x,hx⟩
    let v : F := ⟨y,hy⟩
    have hc : ⁅u,v⁆ ∈ frattini F := commutator_le_frattini_of_nilpotent
      (commutator_mem_commutator (mem_top u) (mem_top v))
    exact mem_map_of_mem N.subtype (hiphi (mem_map_of_mem i hc))
  let f := q.subgroupMap N
  have hf := q.subgroupMap_surjective N
  have hfker : f.ker = frattini N := by
    rw [show f.ker = (q.subgroupMap N).ker from rfl,Subgroup.ker_subgroupMap]
    change (QuotientGroup.mk' K).ker.subgroupOf N = frattini N
    rw [QuotientGroup.ker_mk']
    change ((frattini N).map N.subtype).comap N.subtype = frattini N
    rw [comap_map_eq,N.subtype.ker_eq_bot N.subtype_injective,sup_bot_eq]
  have hDphi : frattini D = ⊥ := frattini_eq_bot_of_ker_eq f hf hfker
  let e : A.subgroupOf D ≃* A := subgroupOfEquivOfLe hAD
  let : IsMulCommutative (A.subgroupOf D) := ⟨⟨fun a b => by
    apply e.injective
    simp only [map_mul,mul_comm]⟩⟩
  have hsplit : ∃ M : Subgroup D, (A.subgroupOf D).IsComplement' M :=
    exists_complement_of_disjoint_frattini _ (by rw [hDphi]; exact disjoint_bot_right)
  have hidx : D.index = N.index := N.index_map_eq hq (by
    change (QuotientGroup.mk' K).ker ≤ N
    rw [QuotientGroup.ker_mk']
    exact hKN)
  have hcop' : (Nat.card A).Coprime D.index := by
    rw [hidx]
    exact hcop.coprime_dvd_left (F.card_map_dvd q)
  obtain ⟨M,hM⟩ := exists_complement_of_coprime_overgroup A D hAD hcop' hsplit
  have hAF : A ≤ frattini (G ⧸ K) := map_le_iff_le_comap.mpr
    (frattini_le_comap_frattini_of_surjective hq)
  have hMt : M = ⊤ := frattini_nongenerating (top_unique (by
    calc
      ⊤ = M ⊔ A := (sup_comm A M ▸ hM.sup_eq_top).symm
      _ ≤ M ⊔ frattini (G ⧸ K) := sup_le_sup_left hAF M))
  have hAbot : A ≤ ⊥ := by simpa only [hMt,inf_top_eq] using hM.disjoint.le_bot
  intro x hx
  exact (QuotientGroup.eq_one_iff x).mp (mem_bot.mp (hAbot (mem_map_of_mem q hx)))

theorem frattini_subgroupOf_le_of_coprime_index (N : Subgroup G) [N.Normal]
    (hFN : frattini G ≤ N) (hcop : (Nat.card (frattini G)).Coprime N.index) :
    (frattini G).subgroupOf N ≤ frattini N := by
  intro x hx
  obtain ⟨y,hy,hyx⟩ := frattini_le_image_of_coprime_index N hFN hcop hx
  have he : y=x := Subtype.ext hyx
  exact he ▸ hy

theorem frattini_subgroupOf_le_of_odd_index_two (N : Subgroup G) [N.Normal]
    (hFN : frattini G ≤ N) (hodd : Odd (Nat.card (frattini G))) (hi : N.index = 2) :
    (frattini G).subgroupOf N ≤ frattini N :=
  frattini_subgroupOf_le_of_coprime_index N hFN (hi ▸ hodd.coprime_two_right)


theorem frattini_subgroupOf_le_of_odd_two_quotient (N : Subgroup G) [N.Normal]
    (hFN : frattini G ≤ N) (hodd : Odd (Nat.card (frattini G)))
    (hquot : IsPGroup 2 (G ⧸ N)) :
    (frattini G).subgroupOf N ≤ frattini N := by
  obtain ⟨n,hn⟩ := hquot.exists_card_eq
  apply frattini_subgroupOf_le_of_coprime_index N hFN
  rw [index_eq_card,hn]
  exact hodd.coprime_two_right.pow_right n

/-- The literal quotient-image form consumed after B.6.8 identifies the odd core with Φ(H/O₂(H)). -/
theorem quotient_image_le_frattini_image_of_odd_index_two
    (Q L J : Subgroup G) [Q.Normal] [L.Normal]
    (hphi : J.map (QuotientGroup.mk' Q) = frattini (G ⧸ Q))
    (hodd : Odd (Nat.card (J.map (QuotientGroup.mk' Q))))
    (hJL : J.map (QuotientGroup.mk' Q) ≤ L.map (QuotientGroup.mk' Q))
    (hi : (L.map (QuotientGroup.mk' Q)).index = 2) :
    J.map (QuotientGroup.mk' Q) ≤
      (frattini (L.map (QuotientGroup.mk' Q))).map (L.map (QuotientGroup.mk' Q)).subtype := by
  let : (L.map (QuotientGroup.mk' Q)).Normal :=
    (inferInstance : L.Normal).map _ (QuotientGroup.mk'_surjective Q)
  rw [hphi] at hodd hJL ⊢
  exact frattini_le_image_of_coprime_index _ hJL (by simpa only [hi] using hodd.coprime_two_right)

end FrattiniCoprime
