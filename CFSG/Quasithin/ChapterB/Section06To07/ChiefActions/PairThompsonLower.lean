module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallResidual

/-!
# The small offender base lies in the original Thompson image

In a solvable reduced minimal parabolic, the best offenders supported inside
a normal subgroup form a stable family. The proved source classification
says that family generates the entire offender subgroup.

For a marked symmetric-five pair, an offender splits as the product of its
coordinate projections. A nontrivial coordinate offender normally generates
its symmetric-five factor. The actual source Sylow exchanger then puts the
second factor in the same normal subgroup. Thus a normal subgroup containing
any offender contains the full paired base.

Apply these results to the image of the original global elementary Thompson
subgroup, which is normal and contains the original maximum elementary actor.
All maps and the distinguished offender remain the literal chief-action maps.
This supplies the lower bound in original 3.1.9(5), printed pp.577–578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction BinaryPermutation

private theorem normal_supported_bestOffenders_stable
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (N : Subgroup D) [N.Normal]
    {A : Subgroup D} (hA : IsOffender ρ A) (hAN : A ≤ N) :
    IsStable ρ {B | IsBestOffender ρ B ∧ B ≤ N} := by
  obtain ⟨B,hBA,hB⟩ := hA.exists_bestOffender ρ
  refine ⟨⟨B,hB,hBA.trans hAN⟩,fun C hC => hC.1,?_,?_⟩
  · intro C hC g
    exact ⟨hC.1.map_conj ρ g,(map_mono hC.2).trans_eq (Normal.map_conj_eq N g)⟩
  · intro C hC B hB hBC
    exact ⟨hC.1.of_equalWeightLE ρ hB hBC,hBC.1.trans hC.2⟩

theorem solvable_offenderSubgroup_le_normal_of_offender
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (T : Sylow 2 D)
    (hP : IsMinimalParabolicOver T ⊤) (hsolv : Group.IsSolvable D)
    (hcore : pCore 2 D = ⊥) (hf : Function.Injective ρ)
    (N : Subgroup D) [N.Normal]
    {A : Subgroup D} (hA : IsOffender ρ A) (hAN : A ≤ N) :
    offenderSubgroup ρ ≤ N := by
  obtain ⟨d,ht,hstable,hr,hgen⟩ := source_solvable_minimalParabolic_factors
    T hP hsolv hcore hf ⟨A,hA⟩
  rw [←hstable {B | IsBestOffender ρ B ∧ B ≤ N}
    (normal_supported_bestOffenders_stable ρ N hA hAN)]
  exact iSup_le fun B => iSup_le fun hB => hB.1.2

private theorem normal_contains_exchanged_product_of_offender
    {D K W : Type*} [Group D] [Group K] [Finite K]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (τ : Representation (ZMod 2) K W) (hn : ¬ IsStrongFFModule τ)
    (hclose : ∀ (N B : Subgroup K) [N.Normal], IsOffender τ B → B ≤ N → N = ⊤)
    (j : K × K →* D) (N : Subgroup D) [N.Normal] (t : D)
    (hex₁ : (((⊤ : Subgroup K).prod ⊥).map j).map (MulAut.conj t).toMonoidHom =
      ((⊥ : Subgroup K).prod ⊤).map j)
    (hex₂ : (((⊥ : Subgroup K).prod ⊤).map j).map (MulAut.conj t).toMonoidHom =
      ((⊤ : Subgroup K).prod ⊥).map j)
    {A : Subgroup (K × K)}
    (hA : IsOffender (Representation.prod (τ.comp (MonoidHom.fst K K))
      (τ.comp (MonoidHom.snd K K))) A) (hAN : A.map j ≤ N) : j.range ≤ N := by
  obtain ⟨he,h₁,h₂⟩ := offender_product_of_not_strong τ τ hn hn hA
  have hfirst (h : IsOffender τ (A.map (MonoidHom.fst K K))) :
      ((⊤ : Subgroup K).prod ⊥).map j ≤ N := by
    let Q := N.comap (j.comp (MonoidHom.inl K K))
    have hAQ : A.map (MonoidHom.fst K K) ≤ Q := by
      intro a ha
      apply hAN
      apply mem_map_of_mem
      rw [he]
      exact ⟨ha,one_mem _⟩
    have hQ := hclose Q _ h hAQ
    rintro _ ⟨⟨a,b⟩,hab,rfl⟩
    have hb : b = 1 := hab.2
    subst b
    exact show a ∈ Q from hQ ▸ mem_top a
  have hsecond (h : IsOffender τ (A.map (MonoidHom.snd K K))) :
      ((⊥ : Subgroup K).prod ⊤).map j ≤ N := by
    let Q := N.comap (j.comp (MonoidHom.inr K K))
    have hAQ : A.map (MonoidHom.snd K K) ≤ Q := by
      intro a ha
      apply hAN
      apply mem_map_of_mem
      rw [he]
      exact ⟨one_mem _,ha⟩
    have hQ := hclose Q _ h hAQ
    rintro _ ⟨⟨a,b⟩,hab,rfl⟩
    have ha : a = 1 := hab.1
    subst a
    exact show b ∈ Q from hQ ▸ mem_top b
  have hboth : ((⊤ : Subgroup K).prod ⊥).map j ≤ N ∧
      ((⊥ : Subgroup K).prod ⊤).map j ≤ N := by
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · exact (hA.1.1 (by rw [he,h₁,h₂,bot_prod_bot])).elim
      · have h := hsecond h₂
        exact ⟨hex₂ ▸ (map_mono h).trans_eq (Normal.map_conj_eq N t),h⟩
    · have h := hfirst h₁
      exact ⟨h,hex₁ ▸ (map_mono h).trans_eq (Normal.map_conj_eq N t)⟩
  rintro _ ⟨⟨a,b⟩,rfl⟩
  have h₁ : j (a,1) ∈ N := hboth.1 (mem_map_of_mem j ⟨mem_top a,one_mem _⟩)
  have h₂ : j (1,b) ∈ N := hboth.2 (mem_map_of_mem j ⟨one_mem _,mem_top b⟩)
  have he : j (a,b) = j (a,1) * j (1,b) := by rw [←map_mul]; simp
  rw [he]
  exact N.mul_mem h₁ h₂

private theorem normal_eq_top_of_core_five_offender
    (N B : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (hB : IsOffender (coreRepresentation (Fin 5)) B) (hBN : B ≤ N) : N = ⊤ := by
  let e : ActionEquiv (coreRepresentation (Fin 5)) (naturalRepresentation (Fin 5)) := {
    groupEquiv := MulEquiv.refl _
    linearEquiv := coreEquivNatural (Fin 5) (by decide)
    intertwines := coreEquivNatural_equivariant (Fin 5) (by decide) }
  exact normal_eq_top_of_five_offender _ e N B hBN hB

theorem source_pair_five_offenderSubgroup_le_normal
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (T : Sylow 2 D)
    (hP : IsMinimalParabolicOver T ⊤) (hcore : pCore 2 D = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (N : Subgroup D) [N.Normal]
    {A : Subgroup D} (hA : IsOffender ρ A) (hAN : A ≤ N) :
    offenderSubgroup ρ ≤ N := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  obtain ⟨B,hBA,hB⟩ := hA.exists_bestOffender ρ
  have hBY : B ≤ Y := hB.le_offenderSubgroup ρ
  let C := (B.subgroupOf Y).map c.action.groupEquiv.toMonoidHom
  have hB' : IsOffender (ρ.comp Y.subtype) (B.subgroupOf Y) :=
    (hB.isOffender ρ).subgroupOf ρ hBY
  have hC : IsOffender FivePair.action C := by
    let := hB'.1.2
    refine ⟨⟨fun hz => hB'.1.1
      ((map_eq_bot_iff_of_injective _ c.action.groupEquiv.injective).mp hz),
      IsElementaryAbelian.map _⟩, ?_⟩
    rw [rank_map_injective _ c.action.groupEquiv.injective,←c.symmetric_fixedCodim]
    exact hB'.2
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  have hjC : C.map j = B := by
    rw [map_map]
    have hj : j.comp c.action.groupEquiv.toMonoidHom = Y.subtype := by
      ext x
      simp [j]
    rw [hj,map_subgroupOf_eq_of_le hBY]
  obtain ⟨t,ht₁,ht₂⟩ := source_offender_two_factor_exists_sylow_exchange ρ T hP ⟨A,hA⟩ hcore d
  have h₁ : ((⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥).map j = d.first.map Y.subtype := by
    rw [←map_map,c.first_eq]
  have h₂ : ((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤).map j = d.second.map Y.subtype := by
    rw [←map_map,c.second_eq]
  have ht (L : Subgroup Y) :
      (L.map Y.subtype).map (MulAut.conj (t : D)).toMonoidHom =
        (L.map (MulAut.conjNormal (t : D)).toMonoidHom).map Y.subtype := by
    rw [map_map,map_map]
    rfl
  have hN := normal_contains_exchanged_product_of_offender
    (coreRepresentation (Fin 5))
    (fun ⟨E,hE⟩ => Offenders.Odd.not_isStrongOffender_core (Or.inl rfl) E hE)
    normal_eq_top_of_core_five_offender j N t
    (by rw [h₁,h₂,ht,ht₁]) (by rw [h₁,h₂,ht,ht₂]) hC
    (by rw [hjC]; exact hBA.trans hAN)
  intro y hy
  apply hN
  exact ⟨c.action.groupEquiv ⟨y,hy⟩,by simp [j]⟩

theorem small_offenderSubgroup_le_normal_of_offender
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤)
    (hcore : pCore 2 D = ⊥)
    (hsmall : SmallNaturalWreathAction ρ ∨ ChiefFiveMarkedSection ρ ∨
      ∃ d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
        Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5))))
    (N : Subgroup D) [N.Normal]
    {A : Subgroup D} (hA : IsOffender ρ A) (hAN : A ≤ N) : offenderSubgroup ρ ≤ N := by
  rcases hsmall with hs | ⟨hqs,c,⟨e⟩⟩ | ⟨d,⟨c⟩⟩
  · have hsolv : Group.IsSolvable D := by
      let := hs.residual_elementary
      let : Group.IsNilpotent (pResidual 2 D) :=
        (IsElementaryAbelian.isPGroup 3 (pResidual 2 D)).isNilpotent
      let : Group.IsNilpotent (D ⧸ pResidual 2 D) := (isPGroup_quotient_pResidual 2).isNilpotent
      exact (Group.isSolvable_iff_subgroup_quotient (pResidual 2 D)).mpr
        ⟨inferInstance,inferInstance⟩
    exact solvable_offenderSubgroup_le_normal_of_offender ρ T hP hsolv hcore hf N hA hAN
  · let := hi
    obtain ⟨⟨e'⟩,_⟩ := source_quasisimple_five_whole_action ρ hf T hP ⟨A,hA⟩ hcore hqs c e
    rw [normal_eq_top_of_five_offender ρ e' N A hAN hA]
    exact le_top
  · exact source_pair_five_offenderSubgroup_le_normal ρ T hP hcore d c N hA hAN

theorem chief_small_offenderSubgroup_le_thompson_image
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (A : Subgroup D) (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup D))
    (hoff : IsOffender (imageRepresentation ρ) (actionSubgroup ρ A))
    (hsmall : SmallNaturalWreathAction (imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (imageRepresentation ρ) ∨
      ∃ d : SourceTwoFactorCase ((imageRepresentation ρ).comp
        (offenderSubgroup (imageRepresentation ρ)).subtype),
        Nonempty (d.MarkedProduct (naturalRepresentation (Fin 5)))) :
    offenderSubgroup (imageRepresentation ρ) ≤
      (elementaryAbelianMaxJ (⊤ : Subgroup D)).map (actionHom ρ) := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hoff.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [←hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  let J := elementaryAbelianMaxJ (⊤ : Subgroup D)
  let : J.Characteristic := elementaryAbelianMaxJ_top_characteristic
  let : (J.map q).Normal := Subgroup.Normal.map inferInstance q hq
  exact small_offenderSubgroup_le_normal_of_offender _ (imageRepresentation_injective ρ)
    (imageRepresentation_irreducible ρ inferInstance) (S.mapSurjective hq)
    (minimalParabolic_reduced_image S hS q hq hc hn).2 hc hsmall (J.map q) hoff
    (map_mono ((le_sSup hA).trans (elementaryAbelianMaxJ_sylow_le_top S)))

end CFSG.Quasithin.ChapterB
