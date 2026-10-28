module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductSecondExtension
public import Theory.SpecificGroups.Alternating.FiveExtensionActionEquations

/-!
# The faithful marked terminal quotient in S₅ × S₃

Conjugation on the prescribed K/O₂(K)=A₅ gives the five-letter action.
Pair it with the extended three-letter block action. Modulo K, the order
has odd part at most three, already detected by the onto S₃ projection;
the remaining kernel inside K is O₂(K). Thus the joint kernel is a
two-group, and the reverse core containment identifies it with O₂(Y).

The resulting embedding of the literal Y/O₂(Y) has exact factor images
A₅×1 and 1×A₃. Surjectivity onto the full product is a separate local
Thompson-actor obligation, retained by qt-d-1231-terminal-product.
ComponentAnalysis remains the premise discharged by qt-d-1231-terminal.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.812.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

def componentPermutation (C : P.ComponentAnalysis) :
    normalizer (P.K : Set G) →* Equiv.Perm (Fin 5) :=
  Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr C.quotient).toMonoidHom.comp P.quotientAction)

theorem componentPermutation_on_component (C : P.ComponentAnalysis) (k : P.K) :
    P.componentPermutation C ⟨k,P.K.le_normalizer k.property⟩ =
      (P.componentProjection C k).val := by
  apply Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.injective
  change Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv
    (Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm _) =
      Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv (P.componentProjection C k).val
  rw [MulEquiv.apply_symm_apply,
    Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv_apply]
  apply MulEquiv.ext
  intro a
  obtain ⟨l,rfl⟩ := P.componentProjection_surjective C a
  change C.quotient (P.quotientAction ⟨k,P.K.le_normalizer k.property⟩
    (C.quotient.symm (P.componentProjection C l))) = _
  have hproj : C.quotient.symm (P.componentProjection C l) =
      QuotientGroup.mk' (pCore 2 P.K) l := C.quotient.symm_apply_apply _
  rw [hproj]
  change C.quotient (quotientAut (pCore 2 P.K)
    (P.K.normalizerMonoidHom ⟨k,P.K.le_normalizer k.property⟩)
    (QuotientGroup.mk' (pCore 2 P.K) l)) = _
  rw [quotientAut_apply_mk]
  have he : P.K.normalizerMonoidHom ⟨k,P.K.le_normalizer k.property⟩ l = k*l*k⁻¹ :=
    Subtype.ext rfl
  rw [he]
  change P.componentProjection C (k*l*k⁻¹) =
    P.componentProjection C k * P.componentProjection C l * (P.componentProjection C k)⁻¹
  simp only [map_mul,map_inv]

def firstYAction (C : P.ComponentAnalysis) : P.Y →* Equiv.Perm (Fin 5) :=
  (P.componentPermutation C).comp (inclusion (P.Y_normalizes_component C))

theorem firstYAction_mem_ker (C : P.ComponentAnalysis) (y : P.Y) :
    y ∈ (P.firstYAction C).ker ↔ (y : G) ∈ P.quotientCentralizer := by
  have h : P.firstYAction C y = 1 ↔
      P.quotientAction (inclusion (P.Y_normalizes_component C) y) = 1 := by
    change Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm
      (MulAut.congr C.quotient (P.quotientAction _)) = 1 ↔ _
    rw [map_eq_one_iff _ Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm.injective,
      map_eq_one_iff _ (MulAut.congr C.quotient).injective]
  change P.firstYAction C y = 1 ↔ _
  rw [h]
  constructor
  · intro hy
    exact ⟨inclusion (P.Y_normalizes_component C) y,hy,rfl⟩
  · rintro ⟨n,hn,he⟩
    have he' : n = inclusion (P.Y_normalizes_component C) y := Subtype.ext he
    rwa [←he']

theorem firstYAction_component_image (C : P.ComponentAnalysis) :
    (P.K.subgroupOf P.Y).map (P.firstYAction C) = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rintro a ⟨y,hy,rfl⟩
    change P.componentPermutation C ⟨y,_⟩ ∈ alternatingGroup (Fin 5)
    rw [P.componentPermutation_on_component C ⟨y,hy⟩]
    exact (P.componentProjection C ⟨y,hy⟩).property
  · intro a ha
    obtain ⟨k,hk⟩ := P.componentProjection_surjective C ⟨a,ha⟩
    exact ⟨inclusion P.component_le_Y k,k.property,
      (P.componentPermutation_on_component C k).trans (congrArg Subtype.val hk)⟩

theorem firstYAction_second_trivial (C : P.ComponentAnalysis) :
    P.L2.subgroupOf P.Y ≤ (P.firstYAction C).ker := by
  intro y hy
  exact (P.firstYAction_mem_ker C y).mpr (P.L2_le_quotientCentralizer hy)

/-- A quotient of odd part at most three has a two-group kernel under an
onto map to S₃. -/
private theorem three_part_kernel_twoGroup {H : Type*} [Group H] [Finite H]
    (q : H →* Equiv.Perm (Fin 3)) (hq : Function.Surjective q)
    (hcard : ∃ n, Nat.card H ∣ 3 * 2^n) : IsPGroup 2 q.ker := by
  obtain ⟨n,hn⟩ := hcard
  have hc : q.ker.index = 6 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hq,Nat.card_congr topEquiv.toEquiv,
      Nat.card_perm,Nat.card_fin]
    decide
  have hd : 3 * Nat.card q.ker ∣ 3 * 2^n := by
    apply dvd_trans ?_ hn
    rw [←q.ker.card_mul_index,hc]
    exact ⟨2,by omega⟩
  exact IsPGroup.of_card_dvd_pow ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hd)

theorem marked_action_twoKernel
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (q : P.Y →* Equiv.Perm (Fin 3)) (hq : Function.Surjective q)
    (hK : P.K.subgroupOf P.Y ≤ q.ker) :
    IsPGroup 2 ((P.firstYAction C).prod q).ker := by
  let K := P.K.subgroupOf P.Y
  let : K.Normal := normal_subgroupOf_of_le_normalizer (P.Y_normalizes_component C)
  let d := QuotientGroup.lift K q hK
  have hd : Function.Surjective d := QuotientGroup.lift_surjective_of_surjective K q hq hK
  have hdp : IsPGroup 2 d.ker := three_part_kernel_twoGroup d hd
    (P.quotient_component_card_bound structural escape C)
  let B := ((P.firstYAction C).prod q).ker
  let f := (QuotientGroup.mk' K).comp B.subtype
  have him : f.range ≤ d.ker := by
    rintro a ⟨b,rfl⟩
    exact congrArg Prod.snd b.property
  have hfp : IsPGroup 2 f.ker := by
    let j : f.ker →* P.K.pCoreIn 2 :=
      (P.Y.subtype.comp (B.subtype.comp f.ker.subtype)).codRestrict _ (fun x => by
        apply P.component_inf_quotientCentralizer_le_core C
        refine ⟨(QuotientGroup.eq_one_iff x.val.val).mp x.property,?_⟩
        exact (P.firstYAction_mem_ker C x.val.val).mp (congrArg Prod.fst x.val.property))
    exact (isPGroup_pCoreIn 2 P.K).of_injective j (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : P.K.pCoreIn 2 => (x : G)) h)
  have hp := (hdp.to_le him).comap_of_ker_isPGroup f hfp
  rw [MonoidHom.comap_range_self] at hp
  exact hp.of_equiv (topEquiv : (⊤ : Subgroup B) ≃* B)

def secondYAction
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Y →* Equiv.Perm (Fin 3) :=
  Classical.choose (P.exists_second_Y_action structural escape C)

theorem secondYAction_component_trivial
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.K.subgroupOf P.Y ≤ (P.secondYAction structural escape C).ker :=
  (Classical.choose_spec (P.exists_second_Y_action structural escape C)).1

theorem secondYAction_agrees
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis)
    (y : P.Y) (hy : (y : G) ∈ P.pointNormalizer) :
    P.secondYAction structural escape C y = P.pointSecondAction ⟨y,hy⟩ :=
  (Classical.choose_spec (P.exists_second_Y_action structural escape C)).2 y hy

theorem secondYAction_surjective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Function.Surjective (P.secondYAction structural escape C) :=
  P.second_Y_action_surjective structural escape C _ (P.secondYAction_agrees structural escape C)

theorem secondYAction_second_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.L2.subgroupOf P.Y).map (P.secondYAction structural escape C) = alternatingGroup (Fin 3) :=
  P.second_Y_action_image structural escape C _ (P.secondYAction_agrees structural escape C)

/-- The prescribed component conjugation and the extended complementary block
form the actual marked homomorphism into S₅×S₃. -/
def markedProductAction
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    P.Y →* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) :=
  (P.firstYAction C).prod (P.secondYAction structural escape C)

theorem markedProductAction_twoKernel
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    IsPGroup 2 (P.markedProductAction structural escape C).ker :=
  P.marked_action_twoKernel structural escape C _
    (P.secondYAction_surjective structural escape C) (P.secondYAction_component_trivial structural escape C)

/-- The ambient two-core acts trivially on the original K/O₂(K). -/
theorem twoCore_le_firstYAction_ker (C : P.ComponentAnalysis) :
    pCore 2 P.Y ≤ (P.firstYAction C).ker := by
  let i : P.K →* P.Y := inclusion P.component_le_Y
  have hcore : (pCore 2 P.Y).comap i ≤ pCore 2 P.K :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective i (inclusion_injective _)⟩
  intro y hy
  apply (P.firstYAction_mem_ker C y).mpr
  let n := inclusion (P.Y_normalizes_component C) y
  refine ⟨n,?_,rfl⟩
  change P.quotientAction n = 1
  apply MulEquiv.ext
  intro a
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P.K) a
  change quotientAut (pCore 2 P.K) (P.K.normalizerMonoidHom n)
    (QuotientGroup.mk' (pCore 2 P.K) k) = _
  rw [quotientAut_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply hcore
  change y * i k * y⁻¹ / i k ∈ pCore 2 P.Y
  rw [div_eq_mul_inv]
  exact (commutator_le_left (pCore 2 P.Y) ⊤)
    (commutator_mem_commutator hy (mem_top (i k)))

theorem markedProductAction_ker
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.markedProductAction structural escape C).ker = pCore 2 P.Y := by
  have hlecore : (P.markedProductAction structural escape C).ker ≤ pCore 2 P.Y :=
    le_sSup ⟨inferInstance,P.markedProductAction_twoKernel structural escape C⟩
  apply le_antisymm hlecore
  rw [markedProductAction,MonoidHom.ker_prod]
  apply le_inf (P.twoCore_le_firstYAction_ker C)
  let q := P.secondYAction structural escape C
  let I := (pCore 2 P.Y).map q
  let : I.Normal := Normal.map inferInstance q (P.secondYAction_surjective structural escape C)
  have hle : I ≤ pCore 2 (Equiv.Perm (Fin 3)) := le_sSup ⟨inferInstance,pCore_isPGroup.map q⟩
  have hz : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id _) Function.surjective_id
      (show IsPGroup 2 (MonoidHom.id (Equiv.Perm (Fin 3))).ker from by
        rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa only [MonoidHom.ker_id] using hh.symm
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hle.trans hz.le))

theorem markedProductAction_first_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.K.subgroupOf P.Y).map (P.markedProductAction structural escape C) =
      (alternatingGroup (Fin 5)).prod ⊥ := by
  apply le_antisymm
  · rintro a ⟨y,hy,rfl⟩
    refine ⟨?_,P.secondYAction_component_trivial structural escape C hy⟩
    exact (P.firstYAction_component_image C).le (mem_map_of_mem _ hy)
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨y,hy,he⟩ := (P.firstYAction_component_image C).symm ▸ ha
    refine ⟨y,hy,Prod.ext he ?_⟩
    exact (P.secondYAction_component_trivial structural escape C hy).trans (mem_bot.mp hb).symm

theorem markedProductAction_second_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.L2.subgroupOf P.Y).map (P.markedProductAction structural escape C) =
      (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3)) := by
  apply le_antisymm
  · rintro a ⟨y,hy,rfl⟩
    refine ⟨P.firstYAction_second_trivial C hy,?_⟩
    exact (P.secondYAction_second_image structural escape C).le (mem_map_of_mem _ hy)
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain ⟨y,hy,he⟩ := (P.secondYAction_second_image structural escape C).symm ▸ hb
    refine ⟨y,hy,Prod.ext ?_ he⟩
    exact (P.firstYAction_second_trivial C hy).trans (mem_bot.mp ha).symm

/-- The original quotient embeds in the product through the original marked map.
Surjectivity is the remaining independent-automizer calculation. -/
def markedQuotientEmbedding
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    (P.Y ⧸ pCore 2 P.Y) →* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) :=
  QuotientGroup.lift _ (P.markedProductAction structural escape C)
    (P.markedProductAction_ker structural escape C).ge

theorem markedQuotientEmbedding_apply
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) (y : P.Y) :
    P.markedQuotientEmbedding structural escape C (QuotientGroup.mk' (pCore 2 P.Y) y) =
      P.markedProductAction structural escape C y := rfl

theorem markedQuotientEmbedding_injective
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Function.Injective (P.markedQuotientEmbedding structural escape C) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro y hy
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P.Y) y
  have hx : x ∈ (P.markedProductAction structural escape C).ker := hy
  rw [P.markedProductAction_ker structural escape C] at hx
  exact (QuotientGroup.eq_one_iff x).mpr hx


end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
