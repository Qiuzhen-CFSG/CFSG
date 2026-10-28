module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentCoverNormality
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original point core and the full seven-letter action

The literal H -> H/O2(H) map sends R1 exactly to the two-core of
L1-star T-star. Separately, in the cubic A7 case, faithful descent
through the component center realizes the full H action inside S7.
Its component image is the actual A7, its restriction agrees with the
existing marking, and the unchanged T supplies a Sylow of its image.
The cubic center lies in L1-star and is fixed by the point two-core.
Thus R1 acts by inner automorphisms in both surviving covers, and its
seven-letter image lies in A7 even if the full action extends to S7.

These are the transports needed for the marked R1 normalizer calculation
in 12.6.26. They do not identify the two-core image under the subsequent
automorphism quotient or assert its model order; those calculations
remain to be supplied before the cubic-cover exclusion.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original point core remains exactly the core of the original
point join after the literal star quotient, whose kernel is a two-group. -/
theorem SourceHypothesis.original_point_core_star
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).R₁ =
      (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ⊔
        Nonabelian.Setup.star H (T : Subgroup G)).pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  let J := E.L₁ ⊔ (T : Subgroup G)
  have hJH : J ≤ H := sup_le
    (fun x hx => hH.1.2 (Or.inl hx)) (fun x hx => hH.1.2 (Or.inr hx))
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  change ((J.pCoreIn 2).subgroupOf H).map q = _
  rw [←pCoreIn_subgroupOf 2 J H hJH,map_pCoreIn_of_ker_isPGroup q hk]
  rw [show J.subgroupOf H = E.L₁.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H from
    subgroupOf_sup (le_sup_left.trans hJH) (le_sup_right.trans hJH),Subgroup.map_sup]
  rfl

/-- The original point two-core fixes the actual cubic component center.
The center lies in the original point residual, and the two normal
subgroups inside the literal point join have coprime orders. -/
theorem SourceHypothesis.original_cubicCenter_point_core_centralizes
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (hc : Nat.card (center (Nonabelian.Setup.star H c.K)) = 3) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).R₁ ≤
      centralizer ((center (Nonabelian.Setup.star H c.K)).map
        (Nonabelian.Setup.star H c.K).subtype : Set (Nonabelian.Setup.Hstar H)) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let Z := (center B).map B.subtype
  let J := Nonabelian.Setup.star H E.L₁ ⊔ Nonabelian.Setup.star H (T : Subgroup G)
  let := (S.original_cubicCenter_component_normal D hZ z hz hH c hc).1
  have hZnorm : (⊤ : Subgroup (Nonabelian.Setup.Hstar H)) ≤ normalizer (Z : Set _) := by
    rw [←B.normalizer_eq_top]
    exact normalizer_le_normalizer_characteristic_image B (center B)
  have hZJ : Z ≤ J := by
    let P : Sylow 3 E.L₁ := default
    exact (S.original_component_center_le_residual_sylow D hZ z hz hTz hH c hc P).trans
      ((map_mono (comap_mono (map_subtype_le _))).trans le_sup_left)
  have hZthree : IsPGroup 3 Z := (IsPGroup.of_card (p := 3) (n := 1) hc).map B.subtype
  have hd : Disjoint Z (J.pCoreIn 2) := hZthree.disjoint_of_coprime (isPGroup_pCoreIn 2 J) (by decide)
  rw [S.original_point_core_star D hZ z hH]
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply (le_inf ?_ ?_).trans hd.eq_bot.le
  · exact le_normalizer_iff_commutator_le_right.mp (le_top.trans hZnorm)
  · exact le_normalizer_iff_commutator_le_left.mp (hZJ.trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))

/-- Any literal full H action sends the original point core to inner
automorphisms in either surviving cubic-cover row. -/
theorem SourceHypothesis.original_cubicCover_point_core_inner_action
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7 ∨
      Chapter1.Section02.LocalModels.IsM22Cover (Nonabelian.Setup.star H c.K))
    (f : H →* MulAut (Nonabelian.Setup.star H c.K))
    (hf : ∀ (x : H) (k : Nonabelian.Setup.star H c.K),
      (f x k : Nonabelian.Setup.Hstar H) =
        QuotientGroup.mk' (pCore 2 H) x * k.val *
          (QuotientGroup.mk' (pCore 2 H) x)⁻¹) :
    ((D.fullSetup hZ T z).R₁.subgroupOf H).map f ≤
      MulAut.innerSubgroup (Nonabelian.Setup.star H c.K) := by
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  have hc : Nat.card (center B) = 3 := by
    rcases hm with ⟨_,⟨e⟩,_⟩|⟨_,⟨e⟩,_⟩ <;> rw [Nat.card_congr e.toEquiv] <;> simp
  have hR := S.original_cubicCenter_point_core_centralizes D hZ z hz hTz hH c hc
  rintro _ ⟨r,hr,rfl⟩
  have hfix (b : B) (hb : b ∈ center B) : f r b = b := by
    apply Subtype.ext
    rw [hf]
    have hh := hR (mem_map_of_mem _ hr) b.val (mem_map_of_mem B.subtype hb)
    rw [←hh,mul_inv_cancel_right]
  rcases hm with ⟨_,_,⟨e⟩⟩|⟨_,_,⟨e⟩⟩
  · exact GLS3.Chapter5.OddCentralCovers.inner_of_fixes_center e hc (f r) hfix
  · exact Sporadic.Mathieu.M22TripleCover.inner_of_fixes_center_of_quotient e hc (f r) hfix

/-- In the cubic A7 row the full action has a faithful seven-letter
realization. The original marked action is its literal central-quotient
action, and the actual original Sylow maps to a Sylow in this overgroup of A7. -/
theorem SourceHypothesis.original_alternatingSevenCover_full_permutation_action
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    (e : (Nonabelian.Setup.star H c.K ⧸ center (Nonabelian.Setup.star H c.K)) ≃*
      alternatingGroup (Fin 7)) :
    ∃ f : H →* Equiv.Perm (Fin 7),
      f.ker = (centralizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H))).comap
        (QuotientGroup.mk' (pCore 2 H)) ∧
      (c.K.subgroupOf H).map f = alternatingGroup (Fin 7) ∧
      ((D.fullSetup hZ T z).R₁.subgroupOf H).map f ≤ alternatingGroup (Fin 7) ∧
      (∀ x : c.localActor, MulAut.centralQuotientAction e (a.action x) =
        MulAut.conjNormal (f (inclusion a.local_le x))) ∧
      ∃ P : Sylow 2 f.range,
        (P : Subgroup f.range).map f.range.subtype = ((T : Subgroup G).subgroupOf H).map f := by
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  obtain ⟨af,haf,hak,ha,hK,_⟩ := S.original_cubicCover_full_action D hZ z hz hH c a (Or.inl hm)
  let permAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide))
  let d : MulAut B →* Equiv.Perm (Fin 7) :=
    permAut.symm.toMonoidHom.comp (MulAut.centralQuotientAction e)
  have hd : Function.Injective d := permAut.symm.injective.comp
    (MulAut.centralQuotientAction_injective e)
  have hdconj (b : B) : d (MulAut.conj b) =
      (e (QuotientGroup.mk' (center B) b) : Equiv.Perm (Fin 7)) := by
    apply permAut.injective
    change permAut (permAut.symm (MulAut.centralQuotientAction e (MulAut.conj b))) = _
    rw [permAut.apply_symm_apply,MulAut.centralQuotientAction_conj]
    rfl
  have hdB : (MulAut.innerSubgroup B).map d = alternatingGroup (Fin 7) := by
    ext y
    constructor
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      rw [hdconj]
      exact (e (QuotientGroup.mk' (center B) b)).property
    · intro hy
      obtain ⟨b,hb⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center B))) ⟨y,hy⟩
      exact ⟨MulAut.conj b,⟨b,rfl⟩,(hdconj b).trans (congrArg Subtype.val hb)⟩
  let f := d.comp af
  refine ⟨f,(MonoidHom.ker_comp_of_injective af d hd).trans hak,?_,?_,?_,?_⟩
  · change (c.K.subgroupOf H).map (d.comp af) = _
    rw [←map_map,hK,hdB]
  · change ((D.fullSetup hZ T z).R₁.subgroupOf H).map (d.comp af) ≤ _
    rw [←map_map,←hdB]
    exact map_mono (S.original_cubicCover_point_core_inner_action D hZ z hz hTz hH c
      (Or.inl hm) af haf)
  · intro x
    rw [←ha]
    change MulAut.centralQuotientAction e (af (inclusion a.local_le x)) =
      permAut (permAut.symm (MulAut.centralQuotientAction e (af (inclusion a.local_le x))))
    exact (permAut.apply_symm_apply _).symm
  · have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
    refine ⟨(T.subtype hTH).mapSurjective f.rangeRestrict_surjective,?_⟩
    rw [Sylow.coe_mapSurjective,Sylow.coe_subtype,map_map]
    rfl

end CFSG.Quasithin.Chapter12.Section06
