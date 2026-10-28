module
public import Stellmacher.ElementaryAbelianMaxPair.CoreNormalizers
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonPairSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearFourThompsonPairSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearFourThompsonSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.IndexTwo
public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Persistence
/-! # The original two-member-family normalizer bound
Under the temporary hypothesis that J(S) intersect O₂(H) is elementary, the
proved Thompson products give precisely two maximum elementary subgroups.
Each contains the original marked central involution z, so its ambient
normalizer has characteristic two by 1.1.4(3). The intrinsic pair action
supplies an index-at-most-two beta subgroup and a normalizer inside T of
order at least |S|. Both Γ₀ maximalities then force that normalizer into M.

The centralizing-core argument discharges the normalization input from the
actual Thompson product. The final three model endpoints retain only the
original hypotheses and the temporary Frattini assumption; no new local,
core-normalizer, action or cardinality premise is left.
Source: Aschbacher--Smith 2.5.7, printed p.555. The subsequent root-parabolic
escape is a separate step, needed to refute the temporary assumption.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.maxFamily_pair_large_normalizer
    (c:MathieuSourceSetup H L M S z)
    (hp:∃ V W:Subgroup H,V≠W ∧ elementaryAbelianMaxSubgroups (S:Subgroup H)={V,W}) :
    ∃ A B:Subgroup G,A≠B ∧
      elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)={A,B} ∧
      Nat.card ((S:Subgroup H).map H.subtype)≤
        Nat.card ((c.T:Subgroup G)⊓normalizer ((S:Subgroup H).map H.subtype:Set G)⊓normalizer (A:Set G):Subgroup G) := by
  obtain ⟨V,W,hne,hp⟩:=hp
  have hne':V.map H.subtype≠W.map H.subtype:=fun he=>hne (map_injective H.subtype_injective he)
  have hp':=maxFamily_pair_map H.subtype H.subtype_injective (S:Subgroup H) V W hp
  let : Group.IsNilpotent (c.T:Subgroup G):=c.T.isPGroup'.isNilpotent
  exact ⟨V.map H.subtype,W.map H.subtype,hne',hp',
    pair_normalizer_card_ge _ _ _ _ c.sylow_lt hp' hne'⟩

theorem MathieuSourceSetup.pair_normalizers_mem_beta
    (c:MathieuSourceSetup H L M S z) {C:GroupClass} (hG:IsSimpleQTKE C G)
    (A B:Subgroup G) (hne:A≠B)
    (hp:elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)={A,B})
    (hcore:twoCore H≤normalizer (A:Set G)) :
    ((S:Subgroup H).map H.subtype⊓normalizer (A:Set G))∈beta M ∧
    ((c.T:Subgroup G)⊓normalizer ((S:Subgroup H).map H.subtype:Set G)⊓normalizer (A:Set G))∈beta M := by
  let Y:Subgroup G:=(S:Subgroup H).map H.subtype
  let R:=Y⊓normalizer (A:Set G)
  let Q:Subgroup G:=(c.T:Subgroup G)⊓normalizer (Y:Set G)⊓normalizer (A:Set G)
  have hA:A∈elementaryAbelianMaxSubgroups Y:=hp.symm ▸ Set.mem_insert _ _
  have hAR:A≤R:=le_inf hA.1 A.le_normalizer
  have hJR:elementaryAbelianMaxJ Y≤R:=le_inf (sSup_le fun _ h=>h.1)
    (maxJ_le_normalizer_of_pair Y A B hp hne)
  have hRS:R≤Y:=inf_le_left
  have hQR:twoCore H≤R:=le_inf (pCoreIn_le_sylow H S) hcore
  have hCR:Y⊓centralizer (R:Set G)≤R:=by
    exact le_inf inf_le_left (inf_le_right.trans ((centralizer_le hAR).trans (Subgroup.centralizer_le_normalizer _)))
  have hi:R.relIndex Y≤2:=by
    dsimp only [R]
    rw [inf_relIndex_left]
    exact normalizer_relIndex_le_two_of_pair Y A B Y hp hne Y.le_normalizer
  have hRb:R∈beta M:=by
    have hn:R.relIndex Y≠0:=index_ne_zero_of_finite
    have hcases:R.relIndex Y=1 ∨ R.relIndex Y=2:=by omega
    rcases hcases with hi | hi
    · have he:R=Y:=le_antisymm hRS (relIndex_eq_one.mp hi)
      rw [he]
      exact beta_mono c.pair.1.1 c.base_le (S.isPGroup'.map H.subtype)
    · exact lemma_2_3_9_8 hG c.T c.maximal c.sylow_le c.unique c.gamma c.pair S c.base_le
        hJR hQR hRS hi hCR
  have hRQ:R≤Q:=by
    exact le_inf (le_inf (hRS.trans c.sylow_lt.le) (hRS.trans Y.le_normalizer)) inf_le_right
  exact ⟨hRb,beta_mono hRb hRQ (c.T.isPGroup'.to_le (inf_le_left.trans inf_le_left))⟩

/-- The maximality step shared by both characteristic-two normalizers in
2.5.7. The local subgroup and its beta base are literal source witnesses. -/
theorem gammaZero_large_local_base_false {X U:Subgroup G}
    (hH:H∈gammaZero (Chapter1.He G) M)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hp:(U,X)∈localPairs (Chapter1.He G) M)
    (hcard:twoPart H≤Nat.card U) : False := by
  have hx:=localPair_snd_mem_gamma hp
  have hsize:twoPart H≤twoPart X:=hcard.trans (beta_card_le_twoPart hp.1 hp.2.2.2.1)
  have hzero:X∈gammaZero (Chapter1.He G) M:=by
    rcases hH with hs | hm
    · apply Or.inl
      apply (gammaStar_of_twoPart_le hs ?_ hsize).1
      refine ⟨hx,(U,X),⟨hp,le_rfl⟩,?_⟩
      intro V hV
      exact (gammaZero_card_bound (Or.inl hs) hV).trans hcard
    · exact Or.inr (gammaMax_of_twoPart_le hm hx hsize).1
  have he:X∈gammaEvenZero (Chapter1.He G) M:=⟨hzero,hp.2.1⟩
  rw [hempty] at he
  exact he

/-- Every largest elementary subgroup contains the marked central involution,
so its actual ambient normalizer has characteristic two. -/
theorem MathieuSourceSetup.maxFamily_mem_S2e
    (c:MathieuSourceSetup H L M S z) {C:GroupClass} (hG:IsSimpleQTKE C G)
    {A:Subgroup G} (hA:A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)) :
    A∈Chapter1.S2e G := by
  have hz:z∈A:=mem_maxFamily_of_central_involution hA (c.center_le c.mem_center)
    (by simpa only [c.involution] using pow_orderOf_eq_one z) (by
      intro a ha
      obtain ⟨w,hw,he⟩:=c.mem_center
      have hcomm:=congrArg Subtype.val (mem_center_iff.mp hw ⟨a,c.sylow_lt.le (hA.1 ha)⟩)
      change a*(w:G)=(w:G)*a at hcomm
      change (w:G)=z at he
      rwa [he] at hcomm)
  have hz1:z≠1:=by
    intro he
    have hh:=c.involution
    rw [he,orderOf_one] at hh
    omega
  apply Chapter1.lemma_1_1_4_3 c.T (hG.evenCharacteristic c.T)
    (fun he=>hz1 (mem_bot.mp (show z∈(⊥:Subgroup G) from he ▸ hz))) ((S.isPGroup'.map H.subtype).to_le hA.1)
  intro he
  have hz':z∈(center (c.T:Subgroup G)).map (c.T:Subgroup G).subtype⊓A:=⟨c.mem_center,hz⟩
  exact hz1 (mem_bot.mp (show z∈(⊥:Subgroup G) from he ▸ hz'))

/-- The actual maximum-family normalizer is contained in M. Its
characteristic-two property follows from the original marked z; the
pair action supplies the beta base and the order comparison. -/
theorem MathieuSourceSetup.pair_normalizer_le
    (c:MathieuSourceSetup H L M S z) {C:GroupClass} (hG:IsSimpleQTKE C G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (A B:Subgroup G) (hne:A≠B)
    (hp:elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)={A,B})
    (hcore:twoCore H≤normalizer (A:Set G)) : normalizer (A:Set G)≤M := by
  by_contra hout
  have hA:A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype):=
    hp.symm ▸ Set.mem_insert _ _
  have hAe:=MathieuSourceSetup.maxFamily_mem_S2e c hG hA
  let N:=normalizer (A:Set G)
  have hNcore:twoCore N≠⊥:=by
    intro he
    exact hAe.1 (bot_unique (he ▸ le_pCoreIn_of_normalizes hAe.2.1 A.le_normalizer le_rfl))
  have hb:=(MathieuSourceSetup.pair_normalizers_mem_beta c hG A B hne hp hcore).2
  have hlocal:(((c.T:Subgroup G)⊓normalizer ((S:Subgroup H).map H.subtype:Set G)⊓normalizer (A:Set G)),N)∈
      localPairs (Chapter1.He G) M:=⟨hb,hAe.2.2,hNcore,inf_le_right,hout⟩
  apply gammaZero_large_local_base_false c.gamma hempty hlocal
  rw [←sylow_image_card H S]
  let : Group.IsNilpotent (c.T:Subgroup G):=c.T.isPGroup'.isNilpotent
  exact pair_normalizer_card_ge _ _ A B c.sylow_lt hp hne

theorem MathieuSourceSetup.core_normalizes_maxFamily
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=
      ((S:Subgroup H)⊓L.subgroupOf H)⊔(elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hphi:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥)
    {A:Subgroup H} (hA:A∈elementaryAbelianMaxSubgroups (S:Subgroup H)) :
    pCore 2 H≤normalizer (A:Set H) := by
  have hg:L.subgroupOf H⊔(S:Subgroup H)=⊤:=by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen]
    rw [←MonoidHom.range_eq_map,H.range_subtype]
  have ho:Theory.GroupTheory.componentOrbit (L.subgroupOf H) (S:Subgroup H)=L.subgroupOf H:=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (by rw [normalizer_eq_top];exact le_top)) (Theory.GroupTheory.le_componentOrbit _ _)
  have hc:=c.component.sylow_centralizer_orbit_eq_pCore S hg
  rw [ho] at hc
  have hKC:pCore 2 H≤centralizer (L.subgroupOf H:Set H):=by rw [←hc];exact inf_le_right
  let R:=elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H
  have hR:IsPGroup 2 R:=(pCore_isPGroup (p:=2) (G:=H)).to_le inf_le_right
  let : Fact (IsPGroup 2 R):=⟨hR⟩
  let : IsElementaryAbelian 2 R:=(frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp hphi
  exact maxFamily_core_normalizes (S:Subgroup H) ((S:Subgroup H)⊓L.subgroupOf H) (pCore 2 H)
    (pCore_isPGroup.le_sylow_of_normal S) (hKC.trans (centralizer_le inf_le_right)) hJ hA

/-- The intrinsic pair and the Thompson product discharge all group-action
premises in the source normalizer bound. -/
theorem MathieuSourceSetup.maxFamily_normalizers_le_of_thompson_product
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    {C:GroupClass} (hG:IsSimpleQTKE C G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=
      ((S:Subgroup H)⊓L.subgroupOf H)⊔(elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hphi:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥)
    (hp:∃V W:Subgroup H,V≠W ∧ elementaryAbelianMaxSubgroups (S:Subgroup H)={V,W}) :
    ∀A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype),normalizer (A:Set G)≤M := by
  obtain ⟨V,W,hne,hp⟩:=hp
  have hp':=maxFamily_pair_map H.subtype H.subtype_injective (S:Subgroup H) V W hp
  have hne':V.map H.subtype≠W.map H.subtype:=fun he=>hne (map_injective H.subtype_injective he)
  have hcore (A:Subgroup H) (hA:A∈elementaryAbelianMaxSubgroups (S:Subgroup H)) :
      twoCore H≤normalizer (A.map H.subtype:Set G):=
    (map_mono (MathieuSourceSetup.core_normalizes_maxFamily c hgen hJ hphi hA)).trans
      (A.le_normalizer_map H.subtype)
  intro A hA
  rw [hp'] at hA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with rfl | rfl
  · exact MathieuSourceSetup.pair_normalizer_le c hG hempty _ _ hne' hp'
      (hcore V (hp.symm ▸ Set.mem_insert _ _))
  · exact MathieuSourceSetup.pair_normalizer_le c hG hempty _ _ hne'.symm
      (hp'.trans (Set.pair_comm _ _))
      (hcore W (hp.symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)))

open scoped MatrixGroups in
theorem MathieuSourceSetup.linear_simple_maxFamily_normalizers_le_of_frattini_eq_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (hphi:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥) :
    ∀A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype),normalizer (A:Set G)≤M := by
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  exact MathieuSourceSetup.maxFamily_normalizers_le_of_thompson_product c hG hempty hgen
    (MathieuSourceSetup.linear_simple_thompson_product c hG sourceC hempty hgen F hn hF e) hphi
    (MathieuSourceSetup.linear_simple_maxFamily_pair_of_frattini_eq_bot c hG sourceC hempty hgen F hn hF e hphi)

theorem MathieuSourceSetup.linear_four_maxFamily_normalizers_le_of_frattini_eq_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (hphi:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥) :
    ∀A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype),normalizer (A:Set G)≤M := by
  have hF:Nat.card Matrix.PSL3Four.F=2^2:=by simpa using Matrix.PSL3Four.card_F
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty Matrix.PSL3Four.F
    (by decide : 1<2) hF e
  exact MathieuSourceSetup.maxFamily_normalizers_le_of_thompson_product c hG hempty hgen
    (MathieuSourceSetup.linear_four_thompson_product c hG sourceC hempty hgen e) hphi
    (MathieuSourceSetup.linear_four_maxFamily_pair_of_frattini_eq_bot c hG sourceC hempty hgen e hphi)

private noncomputable def centerQuotientEquiv {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

theorem MathieuSourceSetup.symplectic_maxFamily_normalizers_le_of_frattini_eq_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*Theory.SpecificGroups.SymplecticFour.Sp F)
    (hphi:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥) :
    ∀A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype),normalizer (A:Set G)≤M := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let := MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF (centerQuotientEquiv e)
  exact MathieuSourceSetup.maxFamily_normalizers_le_of_thompson_product c hG hempty hgen
    (MathieuSourceSetup.symplectic_thompson_product c hG sourceC hempty hgen F hn hF e) hphi
    (MathieuSourceSetup.symplectic_maxFamily_pair_of_frattini_eq_bot c hG sourceC hempty hgen F hn hF e hphi)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
