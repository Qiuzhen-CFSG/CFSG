module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar11

/-!
# Exact product checks on rows 704 through 767

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block11

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t704 tb704 ts704 _ _ ts704_sum ts704_parity
  apply product_cons_b t705 tb705 ts705 _ _ ts705_sum ts705_parity
  apply product_cons_b t706 tb706 ts706 _ _ ts706_sum ts706_parity
  apply product_cons_b t707 tb707 ts707 _ _ ts707_sum ts707_parity
  apply product_cons_b t708 tb708 ts708 _ _ ts708_sum ts708_parity
  apply product_cons_b t709 tb709 ts709 _ _ ts709_sum ts709_parity
  apply product_cons_b t710 tb710 ts710 _ _ ts710_sum ts710_parity
  apply product_cons_b t711 tb711 ts711 _ _ ts711_sum ts711_parity
  apply product_cons_b t712 tb712 ts712 _ _ ts712_sum ts712_parity
  apply product_cons_b t713 tb713 ts713 _ _ ts713_sum ts713_parity
  apply product_cons_b t714 tb714 ts714 _ _ ts714_sum ts714_parity
  apply product_cons_b t715 tb715 ts715 _ _ ts715_sum ts715_parity
  apply product_cons_b t716 tb716 ts716 _ _ ts716_sum ts716_parity
  apply product_cons_b t717 tb717 ts717 _ _ ts717_sum ts717_parity
  apply product_cons_b t718 tb718 ts718 _ _ ts718_sum ts718_parity
  apply product_cons_b t719 tb719 ts719 _ _ ts719_sum ts719_parity
  apply product_cons_b t720 tb720 ts720 _ _ ts720_sum ts720_parity
  apply product_cons_b t721 tb721 ts721 _ _ ts721_sum ts721_parity
  apply product_cons_b t722 tb722 ts722 _ _ ts722_sum ts722_parity
  apply product_cons_b t723 tb723 ts723 _ _ ts723_sum ts723_parity
  apply product_cons_b t724 tb724 ts724 _ _ ts724_sum ts724_parity
  apply product_cons_b t725 tb725 ts725 _ _ ts725_sum ts725_parity
  apply product_cons_b t726 tb726 ts726 _ _ ts726_sum ts726_parity
  apply product_cons_b t727 tb727 ts727 _ _ ts727_sum ts727_parity
  apply product_cons_b t728 tb728 ts728 _ _ ts728_sum ts728_parity
  apply product_cons_b t729 tb729 ts729 _ _ ts729_sum ts729_parity
  apply product_cons_b t730 tb730 ts730 _ _ ts730_sum ts730_parity
  apply product_cons_b t731 tb731 ts731 _ _ ts731_sum ts731_parity
  apply product_cons_b t732 tb732 ts732 _ _ ts732_sum ts732_parity
  apply product_cons_b t733 tb733 ts733 _ _ ts733_sum ts733_parity
  apply product_cons_b t734 tb734 ts734 _ _ ts734_sum ts734_parity
  apply product_cons_b t735 tb735 ts735 _ _ ts735_sum ts735_parity
  apply product_cons_b t736 tb736 ts736 _ _ ts736_sum ts736_parity
  apply product_cons_b t737 tb737 ts737 _ _ ts737_sum ts737_parity
  apply product_cons_b t738 tb738 ts738 _ _ ts738_sum ts738_parity
  apply product_cons_b t739 tb739 ts739 _ _ ts739_sum ts739_parity
  apply product_cons_b t740 tb740 ts740 _ _ ts740_sum ts740_parity
  apply product_cons_b t741 tb741 ts741 _ _ ts741_sum ts741_parity
  apply product_cons_b t742 tb742 ts742 _ _ ts742_sum ts742_parity
  apply product_cons_b t743 tb743 ts743 _ _ ts743_sum ts743_parity
  apply product_cons_b t744 tb744 ts744 _ _ ts744_sum ts744_parity
  apply product_cons_b t745 tb745 ts745 _ _ ts745_sum ts745_parity
  apply product_cons_b t746 tb746 ts746 _ _ ts746_sum ts746_parity
  apply product_cons_b t747 tb747 ts747 _ _ ts747_sum ts747_parity
  apply product_cons_b t748 tb748 ts748 _ _ ts748_sum ts748_parity
  apply product_cons_b t749 tb749 ts749 _ _ ts749_sum ts749_parity
  apply product_cons_b t750 tb750 ts750 _ _ ts750_sum ts750_parity
  apply product_cons_b t751 tb751 ts751 _ _ ts751_sum ts751_parity
  apply product_cons_b t752 tb752 ts752 _ _ ts752_sum ts752_parity
  apply product_cons_b t753 tb753 ts753 _ _ ts753_sum ts753_parity
  apply product_cons_b t754 tb754 ts754 _ _ ts754_sum ts754_parity
  apply product_cons_b t755 tb755 ts755 _ _ ts755_sum ts755_parity
  apply product_cons_b t756 tb756 ts756 _ _ ts756_sum ts756_parity
  apply product_cons_b t757 tb757 ts757 _ _ ts757_sum ts757_parity
  apply product_cons_b t758 tb758 ts758 _ _ ts758_sum ts758_parity
  apply product_cons_b t759 tb759 ts759 _ _ ts759_sum ts759_parity
  apply product_cons_b t760 tb760 ts760 _ _ ts760_sum ts760_parity
  apply product_cons_b t761 tb761 ts761 _ _ ts761_sum ts761_parity
  apply product_cons_b t762 tb762 ts762 _ _ ts762_sum ts762_parity
  apply product_cons_b t763 tb763 ts763 _ _ ts763_sum ts763_parity
  apply product_cons_b t764 tb764 ts764 _ _ ts764_sum ts764_parity
  apply product_cons_b t765 tb765 ts765 _ _ ts765_sum ts765_parity
  apply product_cons_b t766 tb766 ts766 _ _ ts766_sum ts766_parity
  apply product_cons_b t767 tb767 ts767 _ _ ts767_sum ts767_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d704 da704 ds704 _ _ ds704_sum ds704_parity
  apply product_cons_a d705 da705 ds705 _ _ ds705_sum ds705_parity
  apply product_cons_a d706 da706 ds706 _ _ ds706_sum ds706_parity
  apply product_cons_a d707 da707 ds707 _ _ ds707_sum ds707_parity
  apply product_cons_a d708 da708 ds708 _ _ ds708_sum ds708_parity
  apply product_cons_a d709 da709 ds709 _ _ ds709_sum ds709_parity
  apply product_cons_a d710 da710 ds710 _ _ ds710_sum ds710_parity
  apply product_cons_a d711 da711 ds711 _ _ ds711_sum ds711_parity
  apply product_cons_a d712 da712 ds712 _ _ ds712_sum ds712_parity
  apply product_cons_a d713 da713 ds713 _ _ ds713_sum ds713_parity
  apply product_cons_a d714 da714 ds714 _ _ ds714_sum ds714_parity
  apply product_cons_a d715 da715 ds715 _ _ ds715_sum ds715_parity
  apply product_cons_a d716 da716 ds716 _ _ ds716_sum ds716_parity
  apply product_cons_a d717 da717 ds717 _ _ ds717_sum ds717_parity
  apply product_cons_a d718 da718 ds718 _ _ ds718_sum ds718_parity
  apply product_cons_a d719 da719 ds719 _ _ ds719_sum ds719_parity
  apply product_cons_a d720 da720 ds720 _ _ ds720_sum ds720_parity
  apply product_cons_a d721 da721 ds721 _ _ ds721_sum ds721_parity
  apply product_cons_a d722 da722 ds722 _ _ ds722_sum ds722_parity
  apply product_cons_a d723 da723 ds723 _ _ ds723_sum ds723_parity
  apply product_cons_a d724 da724 ds724 _ _ ds724_sum ds724_parity
  apply product_cons_a d725 da725 ds725 _ _ ds725_sum ds725_parity
  apply product_cons_a d726 da726 ds726 _ _ ds726_sum ds726_parity
  apply product_cons_a d727 da727 ds727 _ _ ds727_sum ds727_parity
  apply product_cons_a d728 da728 ds728 _ _ ds728_sum ds728_parity
  apply product_cons_a d729 da729 ds729 _ _ ds729_sum ds729_parity
  apply product_cons_a d730 da730 ds730 _ _ ds730_sum ds730_parity
  apply product_cons_a d731 da731 ds731 _ _ ds731_sum ds731_parity
  apply product_cons_a d732 da732 ds732 _ _ ds732_sum ds732_parity
  apply product_cons_a d733 da733 ds733 _ _ ds733_sum ds733_parity
  apply product_cons_a d734 da734 ds734 _ _ ds734_sum ds734_parity
  apply product_cons_a d735 da735 ds735 _ _ ds735_sum ds735_parity
  apply product_cons_a d736 da736 ds736 _ _ ds736_sum ds736_parity
  apply product_cons_a d737 da737 ds737 _ _ ds737_sum ds737_parity
  apply product_cons_a d738 da738 ds738 _ _ ds738_sum ds738_parity
  apply product_cons_a d739 da739 ds739 _ _ ds739_sum ds739_parity
  apply product_cons_a d740 da740 ds740 _ _ ds740_sum ds740_parity
  apply product_cons_a d741 da741 ds741 _ _ ds741_sum ds741_parity
  apply product_cons_a d742 da742 ds742 _ _ ds742_sum ds742_parity
  apply product_cons_a d743 da743 ds743 _ _ ds743_sum ds743_parity
  apply product_cons_a d744 da744 ds744 _ _ ds744_sum ds744_parity
  apply product_cons_a d745 da745 ds745 _ _ ds745_sum ds745_parity
  apply product_cons_a d746 da746 ds746 _ _ ds746_sum ds746_parity
  apply product_cons_a d747 da747 ds747 _ _ ds747_sum ds747_parity
  apply product_cons_a d748 da748 ds748 _ _ ds748_sum ds748_parity
  apply product_cons_a d749 da749 ds749 _ _ ds749_sum ds749_parity
  apply product_cons_a d750 da750 ds750 _ _ ds750_sum ds750_parity
  apply product_cons_a d751 da751 ds751 _ _ ds751_sum ds751_parity
  apply product_cons_a d752 da752 ds752 _ _ ds752_sum ds752_parity
  apply product_cons_a d753 da753 ds753 _ _ ds753_sum ds753_parity
  apply product_cons_a d754 da754 ds754 _ _ ds754_sum ds754_parity
  apply product_cons_a d755 da755 ds755 _ _ ds755_sum ds755_parity
  apply product_cons_a d756 da756 ds756 _ _ ds756_sum ds756_parity
  apply product_cons_a d757 da757 ds757 _ _ ds757_sum ds757_parity
  apply product_cons_a d758 da758 ds758 _ _ ds758_sum ds758_parity
  apply product_cons_a d759 da759 ds759 _ _ ds759_sum ds759_parity
  apply product_cons_a d760 da760 ds760 _ _ ds760_sum ds760_parity
  apply product_cons_a d761 da761 ds761 _ _ ds761_sum ds761_parity
  apply product_cons_a d762 da762 ds762 _ _ ds762_sum ds762_parity
  apply product_cons_a d763 da763 ds763 _ _ ds763_sum ds763_parity
  apply product_cons_a d764 da764 ds764 _ _ ds764_sum ds764_parity
  apply product_cons_a d765 da765 ds765 _ _ ds765_sum ds765_parity
  apply product_cons_a d766 da766 ds766 _ _ ds766_sum ds766_parity
  apply product_cons_a d767 da767 ds767 _ _ ds767_sum ds767_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 704).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 704).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 704).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 704).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 704).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 704).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 704).take 64) RightCertificate.wideSecond ((tbRows.drop 704).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 704).take 64) RightCertificate.wideFirst ((daRows.drop 704).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block11
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
