module
public import Theory.SpecificGroups.BinaryFiveAffine.ResidualFixedFour
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.SylowCentralizerConjugacy
public section
/-!
# Transporting the marked affine involution-centralizer packet

An affine marking identifies the actual involution centralizer with D₈ × S₄
and its two-residual with A₄. Transport through the subgroup inclusion retains
the actual module, residual image, and the four fixed vectors. The two weight-four
vectors are conjugates under the original two-residual of the marked central
vector.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
namespace BinaryFiveAffine
open Subgroup
variable {H : Type*} [Group H]

abbrev markedCentralizer (e : H ≃* W) : Subgroup H :=
  Subgroup.centralizer ({e.symm t} : Set H)

theorem markedCentralizer_map (e : H ≃* W) :
    (markedCentralizer e).map e.toMonoidHom=centralizer := by
  simp only [markedCentralizer,Theory.GroupTheory.map_centralizer_equiv,
    Set.image_singleton,e.apply_symm_apply,centralizer]

noncomputable def markedCentralizerEquiv (e : H ≃* W) :
    markedCentralizer e ≃* centralizer :=
  (e.subgroupMap (markedCentralizer e)).trans
    (MulEquiv.subgroupCongr (markedCentralizer_map e))

@[simp] theorem markedCentralizerEquiv_val (e : H ≃* W) (x : markedCentralizer e) :
    (markedCentralizerEquiv e x).val=e x.val := by rfl

noncomputable def markedProductEquiv (e : H ≃* W) :
    markedCentralizer e ≃* DihedralGroup 4 × Equiv.Perm (Fin 4) :=
  (markedCentralizerEquiv e).trans productEquiv.symm

noncomputable def markedResidualEquiv (e : H ≃* W) :
    pResidual 2 (markedCentralizer e) ≃* alternatingGroup (Fin 4) :=
  (((markedCentralizerEquiv e).subgroupMap (pResidual 2 (markedCentralizer e))).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 (markedCentralizerEquiv e)))).trans residualEquiv

abbrev markedResidualImage (e : H ≃* W) : Subgroup H :=
  (pResidual 2 (markedCentralizer e)).map (markedCentralizer e).subtype

theorem markedResidualImage_map (e : H ≃* W) :
    (markedResidualImage e).map e.toMonoidHom=residualImage := by
  have he : e.toMonoidHom.comp (markedCentralizer e).subtype =
      centralizer.subtype.comp (markedCentralizerEquiv e).toMonoidHom := rfl
  change ((pResidual 2 (markedCentralizer e)).map (markedCentralizer e).subtype).map _ = _
  rw [map_map,he,←map_map,map_pResidual]
  exact residualImage_def.symm

abbrev markedFixedFour (e : H ≃* W) (U : Subgroup H) : Subgroup H :=
  U ⊓ Subgroup.centralizer (markedResidualImage e : Set H)

theorem markedFixedFour_map (e : H ≃* W) (U : Subgroup H)
    (hU : U.map e.toMonoidHom=vectorGroup) :
    (markedFixedFour e U).map e.toMonoidHom=fixedFour := by
  rw [map_inf _ _ _ e.injective,hU,Theory.GroupTheory.map_centralizer_equiv]
  have hi : e '' (markedResidualImage e : Set H)=(residualImage:Set W) := by
    change e.toMonoidHom '' (markedResidualImage e : Set H)=(residualImage:Set W)
    rw [←coe_map,markedResidualImage_map]
  rw [hi]

theorem markedFixedFour_card (e : H ≃* W) (U : Subgroup H)
    (hU : U.map e.toMonoidHom=vectorGroup) : Nat.card (markedFixedFour e U)=4 := by
  rw [Nat.card_congr (e.subgroupMap (markedFixedFour e U)).toEquiv]
  change Nat.card ((markedFixedFour e U).map e.toMonoidHom)=4
  rw [markedFixedFour_map e U hU]
  exact fixedFour_card

theorem markedFixedFour_members (e : H ≃* W) (U : Subgroup H)
    (hU : U.map e.toMonoidHom=vectorGroup) (w : H) :
    w∈markedFixedFour e U ↔
      w=1 ∨ w=e.symm t ∨ w=e.symm (SemidirectProduct.inl firstSingular) ∨
        w=e.symm (SemidirectProduct.inl secondSingular) := by
  have hh : w∈markedFixedFour e U ↔ e w∈fixedFour := by
    rw [←markedFixedFour_map e U hU,mem_map_equiv,e.symm_apply_apply]
  rw [hh,fixedFour_members]
  constructor
  · intro h
    rcases h with h|h|h|h
    · exact Or.inl (e.injective (h.trans e.map_one.symm))
    · exact Or.inr (Or.inl (e.eq_symm_apply.mpr h))
    · exact Or.inr (Or.inr (Or.inl (e.eq_symm_apply.mpr h)))
    · exact Or.inr (Or.inr (Or.inr (e.eq_symm_apply.mpr h)))
  · intro h
    rcases h with rfl|rfl|rfl|rfl
    · exact Or.inl e.map_one
    · exact Or.inr (Or.inl (e.apply_symm_apply t))
    · exact Or.inr (Or.inr (Or.inl (e.apply_symm_apply _)))
    · exact Or.inr (Or.inr (Or.inr (e.apply_symm_apply _)))

theorem markedCentralizer_card (e : H ≃* W) : Nat.card (markedCentralizer e)=192 := by
  rw [Nat.card_congr (markedCentralizerEquiv e).toEquiv]
  exact card_centralizer

theorem markedCentralizer_not_two [Finite H] (e : H ≃* W) :
    ¬IsPGroup 2 (markedCentralizer e) := by
  intro hp
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [markedCentralizer_card] at hn
  have hd : 3 ∣ 2^n := hn ▸ (by decide : 3∣192)
  have hh := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at hh

theorem pure_even_mem_residual (g : alternatingGroup (Fin 5)) :
    (SemidirectProduct.inr g.val : W)∈pResidual 2 W := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hr : pResidual 2 (alternatingGroup (Fin 5))=⊤ := by
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hp
    let := hN
    by_contra hne
    let : Nontrivial ((alternatingGroup (Fin 5))⧸N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect ((alternatingGroup (Fin 5))⧸N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  let f : alternatingGroup (Fin 5) →* W :=
    (SemidirectProduct.inr : S →* W).comp (alternatingGroup (Fin 5)).subtype
  have hg : g∈pResidual 2 (alternatingGroup (Fin 5)) := by rw [hr]; trivial
  exact map_pResidual_le 2 f (mem_map_of_mem f hg)

theorem markedSingular_conjugates_residual (e : H ≃* W) :
    (∃ g ∈ pResidual 2 H,
      g*e.symm (SemidirectProduct.inl centralSingular)*g⁻¹=e.symm (SemidirectProduct.inl firstSingular)) ∧
    (∃ g ∈ pResidual 2 H,
      g*e.symm (SemidirectProduct.inl centralSingular)*g⁻¹=e.symm (SemidirectProduct.inl secondSingular)) := by
  constructor
  · obtain ⟨g,hg⟩ := firstSingular_conjugate
    refine ⟨e.symm (SemidirectProduct.inr g.val),?_,?_⟩
    · exact map_pResidual_le 2 e.symm.toMonoidHom
        (mem_map_of_mem _ (pure_even_mem_residual g))
    · simpa only [map_mul,map_inv] using congrArg e.symm hg
  · obtain ⟨g,hg⟩ := secondSingular_conjugate
    refine ⟨e.symm (SemidirectProduct.inr g.val),?_,?_⟩
    · exact map_pResidual_le 2 e.symm.toMonoidHom
        (mem_map_of_mem _ (pure_even_mem_residual g))
    · simpa only [map_mul,map_inv] using congrArg e.symm hg

section Ambient
variable {G : Type*} [Group G] (H : Subgroup G) (e : H ≃* W)

abbrev ambientMarkedCentralizer : Subgroup G :=
  H ⊓ Subgroup.centralizer ({((e.symm t : H) : G)} : Set G)

theorem markedCentralizer_ambient_map :
    (markedCentralizer e).map H.subtype=ambientMarkedCentralizer H e :=
  map_subtype_centralizer_singleton H (e.symm t)

noncomputable def ambientMarkedCentralizerEquiv :
    ambientMarkedCentralizer H e ≃* markedCentralizer e :=
  ((markedCentralizer e).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (markedCentralizer_ambient_map H e)) |>.symm

@[simp] theorem ambientMarkedCentralizerEquiv_val (x : ambientMarkedCentralizer H e) :
    (((ambientMarkedCentralizerEquiv H e x) : H) : G)=x.val := by
  have h := congrArg (fun y : ambientMarkedCentralizer H e => y.val)
    ((ambientMarkedCentralizerEquiv H e).symm_apply_apply x)
  exact h

noncomputable def ambientMarkedProductEquiv :
    ambientMarkedCentralizer H e ≃* DihedralGroup 4 × Equiv.Perm (Fin 4) :=
  (ambientMarkedCentralizerEquiv H e).trans (markedProductEquiv e)

noncomputable def ambientMarkedResidualEquiv :
    pResidual 2 (ambientMarkedCentralizer H e) ≃* alternatingGroup (Fin 4) :=
  ((((ambientMarkedCentralizerEquiv H e).subgroupMap
    (pResidual 2 (ambientMarkedCentralizer H e))).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 (ambientMarkedCentralizerEquiv H e))))).trans
      (markedResidualEquiv e)

abbrev ambientMarkedResidualImage : Subgroup G :=
  (pResidual 2 (ambientMarkedCentralizer H e)).map (ambientMarkedCentralizer H e).subtype

theorem markedResidualImage_ambient_map :
    (markedResidualImage e).map H.subtype=ambientMarkedResidualImage H e := by
  have he : H.subtype.comp (markedCentralizer e).subtype =
      (ambientMarkedCentralizer H e).subtype.comp
        (ambientMarkedCentralizerEquiv H e).symm.toMonoidHom := by
    ext x
    rfl
  change ((pResidual 2 (markedCentralizer e)).map (markedCentralizer e).subtype).map _ = _
  rw [map_map,he,←map_map,map_pResidual]

 theorem map_subtype_inf_centralizer (U K : Subgroup H) :
    (U ⊓ Subgroup.centralizer (K : Set H)).map H.subtype =
      U.map H.subtype ⊓ Subgroup.centralizer (K.map H.subtype : Set G) := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨mem_map_of_mem _ hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨k,hk,rfl⟩
    exact congrArg H.subtype (Subgroup.mem_centralizer_iff.mp hx.2 k hk)
  · rintro ⟨⟨x,hx,rfl⟩,hc⟩
    refine mem_map_of_mem _ ⟨hx,Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro k hk
    apply H.subtype_injective
    exact Subgroup.mem_centralizer_iff.mp hc k.val (mem_map_of_mem _ hk)

theorem markedFixedFour_ambient_map (U : Subgroup H) :
    (markedFixedFour e U).map H.subtype =
      U.map H.subtype ⊓ Subgroup.centralizer (ambientMarkedResidualImage H e : Set G) := by
  rw [markedFixedFour,map_subtype_inf_centralizer,markedResidualImage_ambient_map]

theorem ambientMarkedFixedFour_card (U : Subgroup H)
    (hU : U.map e.toMonoidHom=vectorGroup) :
    Nat.card (↥(U.map H.subtype ⊓ Subgroup.centralizer (ambientMarkedResidualImage H e : Set G)))=4 := by
  rw [←markedFixedFour_ambient_map,card_map_of_injective H.subtype_injective]
  exact markedFixedFour_card e U hU

theorem ambientMarkedFixedFour_members (U : Subgroup H)
    (hU : U.map e.toMonoidHom=vectorGroup) (w : G) :
    w∈U.map H.subtype ⊓ Subgroup.centralizer (ambientMarkedResidualImage H e : Set G) ↔
      w=1 ∨ w=((e.symm t : H) : G) ∨
        w=((e.symm (SemidirectProduct.inl firstSingular) : H) : G) ∨
        w=((e.symm (SemidirectProduct.inl secondSingular) : H) : G) := by
  rw [←markedFixedFour_ambient_map]
  constructor
  · rintro ⟨x,hx,rfl⟩
    rcases (markedFixedFour_members e U hU x).mp hx with h|h|h|h
    · exact Or.inl (congrArg H.subtype h)
    · exact Or.inr (Or.inl (congrArg H.subtype h))
    · exact Or.inr (Or.inr (Or.inl (congrArg H.subtype h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg H.subtype h)))
  · intro h
    rcases h with rfl|rfl|rfl|rfl
    · exact mem_map_of_mem _ (one_mem _)
    · exact mem_map_of_mem _ ((markedFixedFour_members e U hU _).mpr (Or.inr (Or.inl rfl)))
    · exact mem_map_of_mem _ ((markedFixedFour_members e U hU _).mpr (Or.inr (Or.inr (Or.inl rfl))))
    · exact mem_map_of_mem _ ((markedFixedFour_members e U hU _).mpr (Or.inr (Or.inr (Or.inr rfl))))

theorem ambientMarkedCentralizer_card : Nat.card (ambientMarkedCentralizer H e)=192 := by
  rw [Nat.card_congr (ambientMarkedCentralizerEquiv H e).toEquiv]
  exact markedCentralizer_card e

theorem ambientMarkedCentralizer_not_two [Finite G] :
    ¬IsPGroup 2 (ambientMarkedCentralizer H e) := by
  intro hp
  exact markedCentralizer_not_two e
    (hp.of_equiv (ambientMarkedCentralizerEquiv H e))

end Ambient
end BinaryFiveAffine
