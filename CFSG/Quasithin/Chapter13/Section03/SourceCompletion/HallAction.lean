module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.MarkedAction
public import Theory.AtlasPort.LinearGroups.G2.BinaryLargePrimeSylow
public import Theory.GroupTheory.TINormalizerControl
/-!
# The original odd Hall actor centralizes the unitary module

The normal component's natural action supplies the actual full automizer
embedding and a compatible Sylow marking. The images of the original Hall
p-subgroup and Sylow subgroup retain their permuting product. The native
large-prime Sylow theorem kills that image. Finally the actual TI property
under N(L), applied to the original nontrivial U, gives normalization of V
for every Hall actor in H∩N(L).

This proves the substantive module step in12.2.11(c). The prior odd-local
control theorem4.4.3 and the parabolic escape4.4.13 remain separate source
producers, as does selection of the Hall actor from E.2.2. No normalizer
escape or bound on n(H) is used as a conclusion-shaped input.
Source: Aschbacher–Smith12.2.11, pp.798–799.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]
omit [Finite G] in
private theorem permutable_map_subgroupOf (N B S:Subgroup G)
    (hBN:B≤N) (hSN:S≤N)
    {Y:Type*} [Group Y] (f:N→*Y)
    (hperm:(B:Set G)*(S:Set G)=(S:Set G)*(B:Set G)) :
    (((B.subgroupOf N).map f):Set Y)*(((S.subgroupOf N).map f):Set Y)=
      (((S.subgroupOf N).map f):Set Y)*(((B.subgroupOf N).map f):Set Y) := by
  have hsub:((B.subgroupOf N):Set N)*((S.subgroupOf N):Set N)=
      ((S.subgroupOf N):Set N)*((B.subgroupOf N):Set N) := by
    apply Set.Subset.antisymm
    · rintro y ⟨b,hb,s,hs,rfl⟩
      obtain ⟨s',hs',b',hb',he⟩:=Set.mem_mul.mp (hperm ▸ (show b.val*s.val∈(B:Set G)*(S:Set G) from Set.mul_mem_mul hb hs))
      exact ⟨⟨s',hSN hs'⟩,hs',⟨b',hBN hb'⟩,hb',Subtype.ext he⟩
    · rintro y ⟨s,hs,b,hb,rfl⟩
      obtain ⟨b',hb',s',hs',he⟩:=Set.mem_mul.mp (hperm.symm ▸ (show s.val*b.val∈(S:Set G)*(B:Set G) from Set.mul_mem_mul hs hb))
      exact ⟨⟨b',hBN hb'⟩,hb',⟨s',hSN hs'⟩,hs',Subtype.ext he⟩
  simpa only [coe_map,Set.image_mul] using congrArg (Set.image f) hsub

/-- Every original p-subgroup with p>3 normalizing the natural module and
permuting with the original Sylow centralizes the module. -/
theorem unitary_permutable_prime_centralizes {p:ℕ} [Fact p.Prime] (hp:3<p)
    (T:Sylow 2 G) (L B:Subgroup G)
    (hLN:L≤normalizer (V:Set G)) (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hBN:B≤normalizer (V:Set G)) (hB:IsPGroup p B)
    (hperm:(B:Set G)*(T:Set G)=(T:Set G)*(B:Set G))
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer V L) v,E0 (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v)) : B≤centralizer (V:Set G) := by
  obtain ⟨rho,E,he,ht,hd⟩:=exists_unitary_sylow_marking T L hLN hNL e E0 he0
  have hinj:Function.Injective rho := by
    intro a b hab
    apply automizerRepresentation_injective V
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [he,he,hab]
  let f:normalizer (V:Set G)→*Atlas.G2.Model F:=rho.comp V.normalizerMonoidHom.rangeRestrict
  let Bm:Subgroup (Atlas.G2.Model F):=(inducedAutomizer V B).map rho
  let Sm:Subgroup (Atlas.G2.Model F):=(inducedAutomizer V (T:Subgroup G)).map rho
  have hBm:IsPGroup p Bm :=
    ((hB.of_injective (subgroupOfEquivOfLe hBN).toMonoidHom
      (subgroupOfEquivOfLe hBN).injective).map V.normalizerMonoidHom.rangeRestrict).map rho
  have hSm:IsPGroup 2 Sm :=
    ((T.2.of_injective (subgroupOfEquivOfLe hTN).toMonoidHom
      (subgroupOfEquivOfLe hTN).injective).map V.normalizerMonoidHom.rangeRestrict).map rho
  have hP:Atlas.G2.BinaryParabolicPair.derivedSylowAmbient≤Sm:=
    derived_sylow_le_induced_sylow T rho hTN ht (hd.trans (map_le_range _ _))
  have hpermm:(Bm:Set (Atlas.G2.Model F))*(Sm:Set (Atlas.G2.Model F))=
      (Sm:Set (Atlas.G2.Model F))*(Bm:Set (Atlas.G2.Model F)) := by
    simpa only [Bm,Sm,inducedAutomizer,map_map,f] using
      permutable_map_subgroupOf (normalizer (V:Set G)) B (T:Subgroup G) hBN hTN f hperm
  have hbot:=Atlas.G2.BinaryLargePrimeSylow.permutable_prime_eq_bot hp Bm Sm hBm hSm hP hpermm
  apply (inducedAutomizer_eq_bot_iff hBN).mp
  exact (map_eq_bot_iff_of_injective _ hinj).mp hbot

/-- The literal Hall subgroup in H∩M centralizes V, with its V-normalization
derived from the original U and the source TI property. -/
theorem source_hall_prime_centralizes {p:ℕ} [Fact p.Prime] (hp:3<p)
    (T:Sylow 2 G) (L B H U:Subgroup G)
    (hLN:L≤normalizer (V:Set G)) (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hTI:∀g∈normalizer (L:Set G),V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V)
    (hU:U≠⊥) (hUV:U≤V) (hHU:H≤normalizer (U:Set G))
    (hBHM:B≤H⊓normalizer (L:Set G)) (hB:IsPGroup p B)
    (hperm:(B:Set G)*(T:Set G)=(T:Set G)*(B:Set G))
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer V L) v,E0 (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v)) : B≤centralizer (V:Set G) := by
  have hBN:B≤normalizer (V:Set G):=
    (le_inf (hBHM.trans inf_le_right) ((hBHM.trans inf_le_left).trans hHU)).trans
      (inf_normalizer_le_of_trivial_intersections hTI hU hUV)
  exact unitary_permutable_prime_centralizes hp T L B hLN hNL hTN hBN hB hperm e E0 he0

/-- The same original Hall actor acts trivially on both V and L/O₂(L).
Perfection of L is derived from its natural action and original two-residual. -/
theorem source_hall_prime_trivial_component_action {p:ℕ} [Fact p.Prime] (hp:3<p)
    (T:Sylow 2 G) (L B H U:Subgroup G)
    (hLN:L≤normalizer (V:Set G)) (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hTI:∀g∈normalizer (L:Set G),V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V)
    (hU:U≠⊥) (hUV:U≤V) (hHU:H≤normalizer (U:Set G))
    (hBHM:B≤H⊓normalizer (L:Set G)) (hB:IsPGroup p B)
    (hres:pResidual 2 L=⊤) (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (hperm:(B:Set G)*(T:Set G)=(T:Set G)*(B:Set G))
    (e:inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer V L) v,E0 (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v)) :
    B≤centralizer (V:Set G) ∧ B≤normalizer (L:Set G) ∧ ⁅B,L⁆≤L.pCoreIn 2 := by
  have hc:=source_hall_prime_centralizes hp T L B H U hLN hNL hTN hTI hU hUV
    hHU hBHM hB hperm e E0 he0
  obtain ⟨rho,E,he,_,hd⟩:=exists_unitary_sylow_marking T L hLN hNL e E0 he0
  have :Group.IsPerfect L:=component_isPerfect_of_unitary_action L rho E he hLN hfaith hres hd
  have hLQ:L≤normalizer (L.pCoreIn 2:Set G):=L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hk:⁅L,centralizer (V:Set G)⁆≤L.pCoreIn 2:=perfect_core_commutator L V hLN hNL
    ((commutator_mono hfaith le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hLQ))
  refine ⟨hc,hBHM.trans inf_le_right,?_⟩
  rw [commutator_comm]
  exact (commutator_mono le_rfl hc).trans hk

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
