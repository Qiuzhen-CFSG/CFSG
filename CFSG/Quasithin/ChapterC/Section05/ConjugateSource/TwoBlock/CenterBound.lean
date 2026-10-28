module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.BorelGeometry
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingNormalizerAction
public import Theory.Representation.BinaryAlternatingFiveFlag.CenterQuotient
/-!
# The center bound for the paired alternating-five Sylow quotient

Write E₀ for the join of the two marked Borel three-spaces and Z₀ for
their fixed lines. A Sylow element central modulo Z₀ cannot exchange
the two disjoint modules. On each block its normalizer action is a
five-point permutation, whose differences lie in the fixed line; the
permutation is therefore trivial. The module-centralizer decompositions
and C_R(K₁K₂) = 1 place the element in the module product. The inner
Sylow exchange then forces each coordinate into its Borel three-space.

This uses the original block markings and their noncommuting conjugators;
no wreath-product identification or normalization by an outside Sylow
element is assumed. Source: Aschbacher--Smith 14.6.9(k), printed p.1027.
-/

public section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open BinaryPermutation BinaryPermutation.AlternatingFiveFlag
variable {G : Type*} [Group G] {R K L : Subgroup G}

private theorem borelMap_range (h : AlternatingPairSetup R K L) :
    h.borelMap.range = sourceModule K := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    exact (h.coordinates.symm v).property
  · intro hx
    exact ⟨h.coordinates ⟨x,hx⟩, congrArg Subtype.val (h.coordinates.symm_apply_apply _)⟩

private theorem pair_mem_lines
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (u v : Multiplicative (core (Fin 5))) :
    h.borelMap u * h'.borelMap v ∈ line.map h.borelMap ⊔ line.map h'.borelMap ↔
      u ∈ line ∧ v ∈ line := by
  rw [←h.borelPairMap_prod h' line line]
  exact mem_map_iff_mem (h.borelPairMap_injective h') (x := (u,v))

private theorem first_mem_lines
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (u : Multiplicative (core (Fin 5)))
    (hu : h.borelMap u ∈ line.map h.borelMap ⊔ line.map h'.borelMap) : u ∈ line := by
  apply ((pair_mem_lines h h' u 1).mp _).1
  simpa using hu

private theorem normalizes_block_of_line_commutators
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (g : G) (hg : g ∈ R)
    (hc : ∀ r ∈ R, ⁅g,r⁆ ∈ line.map h.borelMap ⊔ line.map h'.borelMap) :
    g ∈ normalizer (K : Set G) := by
  rcases h.permutes g hg with he | he
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · have hU : (sourceModule K).map (MulAut.conj g).toMonoidHom = sourceModule L := by
      rw [sourceModule_map_equiv,he]
    have hall (u : Multiplicative (core (Fin 5))) : u ∈ line := by
      have hu : h.borelMap u ∈ sourceModule K := (h.coordinates.symm u).property
      have hv : g * h.borelMap u * g⁻¹ ∈ sourceModule L :=
        hU ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hu
      obtain ⟨v,hv⟩ := (borelMap_range h').ge hv
      have hc' := hc (h.borelMap u) ((h.module_le.trans inf_le_left) hu)
      have heq : ⁅g,h.borelMap u⁆ = h.borelMap u⁻¹ * h'.borelMap v := by
        change (g * h.borelMap u * g⁻¹) * (h.borelMap u)⁻¹ = _
        simpa only [map_inv,hv] using (h.borel_pair_commute h' u⁻¹ v).symm.eq
      rw [heq] at hc'
      exact (line.inv_mem_iff).mp ((pair_mem_lines h h' u⁻¹ v).mp hc').1
    have heq : (line : Subgroup (Multiplicative (core (Fin 5)))) = ⊤ :=
      eq_top_iff.mpr (fun u _ => hall u)
    have hn := line_card
    rw [heq,card_top] at hn
    have hh : Nat.card (Multiplicative (core (Fin 5))) = 16 := by
      rw [←Nat.card_congr h.coordinates.toEquiv]
      exact h.module_card
    rw [hh] at hn
    norm_num at hn

private theorem action_surjective (h : AlternatingPairSetup R K L) :
    Function.Surjective h.action := by
  let s := ChapterB.Offenders.pairSwap 5 0
  have hs : s ∈ ((ChapterB.baumann R).subgroupOf (K ⊔ ChapterB.baumann R)).map h.action := by
    rw [h.baumann_image]
    exact ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide)
  obtain ⟨t,_,ht⟩ := hs
  have even_lift (g : FivePerm) (hg : g ∈ alternatingGroup (Fin 5)) :
      ∃ k, h.action k = g := by
    obtain ⟨k,_,hk⟩ := h.block_image.symm ▸ hg
    exact ⟨k,hk⟩
  intro g
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
  · exact even_lift g (Equiv.Perm.mem_alternatingGroup.mpr hg)
  · have hgs : g * s⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hg]
      have hsign : Equiv.Perm.sign s = -1 := by decide +kernel
      rw [hsign,inv_neg_one,mul_neg_one,neg_neg]
    obtain ⟨k,hk⟩ := even_lift (g*s⁻¹) hgs
    exact ⟨k*t,by rw [map_mul,hk,ht,inv_mul_cancel_right]⟩

private theorem centralizes_module_of_line_commutators
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (g : G) (hg : g ∈ R)
    (hc : ∀ r ∈ R, ⁅g,r⁆ ∈ line.map h.borelMap ⊔ line.map h'.borelMap) :
    g ∈ centralizer (sourceModule K : Set G) := by
  have hn := normalizes_block_of_line_commutators h h' g hg hc
  obtain ⟨q,hker,hcompat⟩ := h.exists_normalizer_action
  let n : normalizer (K : Set G) := ⟨g,hn⟩
  obtain ⟨s,hs⟩ := action_surjective h (q n)
  let inc := inclusion (sup_le K.le_normalizer h.normalizes)
  have hsg : (inc s)⁻¹ * n ∈ q.ker := by
    change q ((inc s)⁻¹ * n) = 1
    rw [map_mul,map_inv,hcompat,hs,inv_mul_cancel]
  have hfix : (s : G)⁻¹ * g ∈ centralizer (sourceModule K : Set G) := hker.le hsg
  have he (v : Multiplicative (core (Fin 5))) :
      h.borelMap (Multiplicative.ofAdd (rho (h.action s) v.toAdd)) =
        g * h.borelMap v * g⁻¹ := by
    have hh := h.equivariant s (h.coordinates.symm v)
    rw [h.coordinates.apply_symm_apply] at hh
    change h.borelMap (Multiplicative.ofAdd (rho (h.action s) v.toAdd)) = _ at hh
    rw [hh]
    have hcomm := hfix (h.borelMap v) (h.coordinates.symm v).property
    calc
      (s:G) * h.borelMap v * (s:G)⁻¹ =
          (s:G) * (h.borelMap v * ((s:G)⁻¹ * g)) * g⁻¹ := by group
      _ = (s:G) * (((s:G)⁻¹ * g) * h.borelMap v) * g⁻¹ := by rw [hcomm]
      _ = g * h.borelMap v * g⁻¹ := by group
  have hs1 : h.action s = 1 := by
    apply permutation_eq_one_of_line_displacements
    intro v
    apply first_mem_lines h h'
    have hh := hc (h.borelMap v)
      ((h.module_le.trans inf_le_left) (h.coordinates.symm v).property)
    have hh' : h.borelMap (Multiplicative.ofAdd (rho (h.action s) v.toAdd - v.toAdd)) =
        ⁅g,h.borelMap v⁆ := by
      rw [ofAdd_sub,map_div,he,div_eq_mul_inv]
      rfl
    rwa [hh']
  have hnker : n ∈ q.ker := by change q n = 1; exact hs.symm.trans hs1
  exact hker.le hnker

variable [Finite G]

private theorem centralizer_pair_le_of_trivial
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (x y : G) (hx : x ∈ normalizer (R : Set G)) (hy : y ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (hnc' : ¬ (sourceModule L).map (MulAut.conj y⁻¹).toMonoidHom ≤
      centralizer (sourceModule L : Set G))
    (hD : R ⊓ centralizer (K ⊔ L : Subgroup G) = ⊥)
    (g : G) (hg : g ∈ R)
    (hgK : g ∈ centralizer (sourceModule K : Set G))
    (hgL : g ∈ centralizer (sourceModule L : Set G)) :
    g ∈ sourceModule K ⊔ sourceModule L := by
  have hp := (h.full_module_centralizer x hx hnc).le ⟨hg,hgK⟩
  change g ∈ (↑(sourceModule K ⊔ (R ⊓ centralizer (K : Set G))) : Set G) at hp
  rw [coe_mul_of_right_le_normalizer_left (sourceModule K)
    (R ⊓ centralizer (K : Set G))
    (inf_le_right.trans ((centralizer_le (map_subtype_le _)).trans
      (Subgroup.centralizer_le_normalizer _)))] at hp
  obtain ⟨u,hu,d,hd,rfl⟩ := hp
  have huL : u ∈ centralizer (sourceModule L : Set G) :=
    centralizer_le (map_subtype_le _) (h'.commute ((map_subtype_le _) hu))
  have hdL : d ∈ centralizer (sourceModule L : Set G) := by
    have hh := (centralizer (sourceModule L : Set G)).mul_mem
      ((centralizer (sourceModule L : Set G)).inv_mem huL) hgL
    simpa using hh
  have hp' := (h'.full_module_centralizer y hy hnc').le ⟨hd.1,hdL⟩
  change d ∈ (↑(sourceModule L ⊔ (R ⊓ centralizer (L : Set G))) : Set G) at hp'
  rw [coe_mul_of_right_le_normalizer_left (sourceModule L)
    (R ⊓ centralizer (L : Set G))
    (inf_le_right.trans ((centralizer_le (map_subtype_le _)).trans
      (Subgroup.centralizer_le_normalizer _)))] at hp'
  obtain ⟨v,hv,e,he,rfl⟩ := hp'
  have hvK : v ∈ centralizer (K : Set G) := h.commute ((map_subtype_le _) hv)
  have heK : e ∈ centralizer (K : Set G) := by
    have hh := (centralizer (K : Set G)).mul_mem
      ((centralizer (K : Set G)).inv_mem hvK) hd.2
    simpa using hh
  have heKL : e ∈ centralizer (K ⊔ L : Subgroup G) := by
    have hh : K ⊔ L ≤ centralizer ({e} : Set G) := by
      apply sup_le
      · exact fun k hk => mem_centralizer_singleton_iff.mpr (heK k hk)
      · exact fun k hk => mem_centralizer_singleton_iff.mpr (he.2 k hk)
    exact fun k hk => mem_centralizer_singleton_iff.mp (hh hk)
  have he1 : e = 1 := show e ∈ (⊥ : Subgroup G) from
    hD ▸ (show e ∈ R ⊓ centralizer (K ⊔ L : Subgroup G) from ⟨he.1,heKL⟩)
  simpa only [he1,mul_one] using mul_mem_sup hu hv

private theorem first_coordinate_three
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (u v : Multiplicative (core (Fin 5)))
    (hc : ∀ r ∈ R, ⁅h.borelMap u * h'.borelMap v,r⁆ ∈
      line.map h.borelMap ⊔ line.map h'.borelMap) : u ∈ three := by
  obtain ⟨s,hs,hsa⟩ := h.pairExchange_mem
  have hex : pairExchange = k₁ := by decide +kernel
  have hact : h.borelMap (Multiplicative.ofAdd (rho k₁ u.toAdd)) =
      (s:G) * h.borelMap u * (s:G)⁻¹ := by
    have hh := h.equivariant s (h.coordinates.symm u)
    rw [h.coordinates.apply_symm_apply,hsa,hex] at hh
    exact hh
  have hcomm := h'.commute hs.2 (h'.borelMap v)
    ((map_subtype_le _) (h'.coordinates.symm v).property)
  change h'.borelMap v * (s:G) = (s:G) * h'.borelMap v at hcomm
  have hfix : (s:G) * h'.borelMap v * (s:G)⁻¹ = h'.borelMap v := by
    rw [←hcomm,mul_inv_cancel_right]
  have he : h.borelMap (Multiplicative.ofAdd (rho k₁ u.toAdd-u.toAdd)) =
      ⁅(s:G),h.borelMap u * h'.borelMap v⁆ := by
    rw [ofAdd_sub,map_div,hact,div_eq_mul_inv]
    change (s:G) * h.borelMap u * (s:G)⁻¹ * (h.borelMap u)⁻¹ =
      (s:G) * (h.borelMap u * h'.borelMap v) * (s:G)⁻¹ *
      (h.borelMap u * h'.borelMap v)⁻¹
    calc
      _ = ((s:G) * h.borelMap u * (s:G)⁻¹) *
          ((s:G) * h'.borelMap v * (s:G)⁻¹) * (h'.borelMap v)⁻¹ * (h.borelMap u)⁻¹ := by
        rw [hfix]
        group
      _ = _ := by group
  apply mem_three_of_exchange_difference
  apply first_mem_lines h h'
  rw [he,←commutatorElement_inv]
  exact (line.map h.borelMap ⊔ line.map h'.borelMap).inv_mem (hc s hs.1)

/-- A source Sylow element central modulo the two marked fixed lines lies
in the product of the two marked Borel three-spaces. -/
theorem AlternatingPairSetup.mem_borel_six_of_line_commutators
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (x y : G) (hx : x ∈ normalizer (R : Set G)) (hy : y ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (hnc' : ¬ (sourceModule L).map (MulAut.conj y⁻¹).toMonoidHom ≤
      centralizer (sourceModule L : Set G))
    (hD : R ⊓ centralizer (K ⊔ L : Subgroup G) = ⊥)
    (g : G) (hg : g ∈ R)
    (hc : ∀ r ∈ R, ⁅g,r⁆ ∈ line.map h.borelMap ⊔ line.map h'.borelMap) :
    g ∈ three.map h.borelMap ⊔ three.map h'.borelMap := by
  have hcg := centralizes_module_of_line_commutators h h' g hg hc
  have hc' : ∀ r ∈ R, ⁅g,r⁆ ∈ line.map h'.borelMap ⊔ line.map h.borelMap := by
    simpa only [sup_comm] using hc
  have hcg' := centralizes_module_of_line_commutators h' h g hg hc'
  have hgA := centralizer_pair_le_of_trivial h h' x y hx hy hnc hnc' hD g hg hcg hcg'
  have hn : sourceModule L ≤ normalizer (sourceModule K : Set G) :=
    ((map_subtype_le _).trans (h.commute.trans
      (centralizer_le (map_subtype_le _)))).trans (Subgroup.centralizer_le_normalizer _)
  change g ∈ (↑(sourceModule K ⊔ sourceModule L) : Set G) at hgA
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at hgA
  obtain ⟨a,ha,b,hb,rfl⟩ := hgA
  obtain ⟨u,rfl⟩ := (borelMap_range h).ge ha
  obtain ⟨v,rfl⟩ := (borelMap_range h').ge hb
  have hu := first_coordinate_three h h' u v hc
  have hv : v ∈ three := by
    apply first_coordinate_three h' h v u
    simpa only [(h.borel_pair_commute h' u v).eq] using hc'
  exact mul_mem_sup (mem_map_of_mem h.borelMap hu) (mem_map_of_mem h'.borelMap hv)

/-- The literal preimage of the center of R/Z₀ is bounded by the paired
Borel six-space; the residual centralizer is an independent hypothesis. -/
theorem AlternatingPairSetup.borel_quotient_center_le
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (x y : G) (hx : x ∈ normalizer (R : Set G)) (hy : y ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (hnc' : ¬ (sourceModule L).map (MulAut.conj y⁻¹).toMonoidHom ≤
      centralizer (sourceModule L : Set G))
    (hD : R ⊓ centralizer (K ⊔ L : Subgroup G) = ⊥)
    [((line.map h.borelMap ⊔ line.map h'.borelMap).subgroupOf R).Normal] :
    ((center (R ⧸ (line.map h.borelMap ⊔ line.map h'.borelMap).subgroupOf R)).comap
      (QuotientGroup.mk' ((line.map h.borelMap ⊔ line.map h'.borelMap).subgroupOf R))).map
        R.subtype ≤ three.map h.borelMap ⊔ three.map h'.borelMap := by
  rintro _ ⟨g,hg,rfl⟩
  apply h.mem_borel_six_of_line_commutators h' x y hx hy hnc hnc' hD g g.property
  intro r hr
  change ⁅g,(⟨r,hr⟩ : R)⁆ ∈ (line.map h.borelMap ⊔ line.map h'.borelMap).subgroupOf R
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' _ ⁅g,(⟨r,hr⟩ : R)⁆ = 1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact (mem_center_iff.mp hg _).symm

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
