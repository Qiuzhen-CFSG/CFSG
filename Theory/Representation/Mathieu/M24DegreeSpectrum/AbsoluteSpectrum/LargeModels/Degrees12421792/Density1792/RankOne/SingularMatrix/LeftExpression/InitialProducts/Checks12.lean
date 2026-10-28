module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar12

/-!
# Exact product checks on rows 768 through 831

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block12

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t768 tb768 ts768 _ _ ts768_sum ts768_parity
  apply product_cons_b t769 tb769 ts769 _ _ ts769_sum ts769_parity
  apply product_cons_b t770 tb770 ts770 _ _ ts770_sum ts770_parity
  apply product_cons_b t771 tb771 ts771 _ _ ts771_sum ts771_parity
  apply product_cons_b t772 tb772 ts772 _ _ ts772_sum ts772_parity
  apply product_cons_b t773 tb773 ts773 _ _ ts773_sum ts773_parity
  apply product_cons_b t774 tb774 ts774 _ _ ts774_sum ts774_parity
  apply product_cons_b t775 tb775 ts775 _ _ ts775_sum ts775_parity
  apply product_cons_b t776 tb776 ts776 _ _ ts776_sum ts776_parity
  apply product_cons_b t777 tb777 ts777 _ _ ts777_sum ts777_parity
  apply product_cons_b t778 tb778 ts778 _ _ ts778_sum ts778_parity
  apply product_cons_b t779 tb779 ts779 _ _ ts779_sum ts779_parity
  apply product_cons_b t780 tb780 ts780 _ _ ts780_sum ts780_parity
  apply product_cons_b t781 tb781 ts781 _ _ ts781_sum ts781_parity
  apply product_cons_b t782 tb782 ts782 _ _ ts782_sum ts782_parity
  apply product_cons_b t783 tb783 ts783 _ _ ts783_sum ts783_parity
  apply product_cons_b t784 tb784 ts784 _ _ ts784_sum ts784_parity
  apply product_cons_b t785 tb785 ts785 _ _ ts785_sum ts785_parity
  apply product_cons_b t786 tb786 ts786 _ _ ts786_sum ts786_parity
  apply product_cons_b t787 tb787 ts787 _ _ ts787_sum ts787_parity
  apply product_cons_b t788 tb788 ts788 _ _ ts788_sum ts788_parity
  apply product_cons_b t789 tb789 ts789 _ _ ts789_sum ts789_parity
  apply product_cons_b t790 tb790 ts790 _ _ ts790_sum ts790_parity
  apply product_cons_b t791 tb791 ts791 _ _ ts791_sum ts791_parity
  apply product_cons_b t792 tb792 ts792 _ _ ts792_sum ts792_parity
  apply product_cons_b t793 tb793 ts793 _ _ ts793_sum ts793_parity
  apply product_cons_b t794 tb794 ts794 _ _ ts794_sum ts794_parity
  apply product_cons_b t795 tb795 ts795 _ _ ts795_sum ts795_parity
  apply product_cons_b t796 tb796 ts796 _ _ ts796_sum ts796_parity
  apply product_cons_b t797 tb797 ts797 _ _ ts797_sum ts797_parity
  apply product_cons_b t798 tb798 ts798 _ _ ts798_sum ts798_parity
  apply product_cons_b t799 tb799 ts799 _ _ ts799_sum ts799_parity
  apply product_cons_b t800 tb800 ts800 _ _ ts800_sum ts800_parity
  apply product_cons_b t801 tb801 ts801 _ _ ts801_sum ts801_parity
  apply product_cons_b t802 tb802 ts802 _ _ ts802_sum ts802_parity
  apply product_cons_b t803 tb803 ts803 _ _ ts803_sum ts803_parity
  apply product_cons_b t804 tb804 ts804 _ _ ts804_sum ts804_parity
  apply product_cons_b t805 tb805 ts805 _ _ ts805_sum ts805_parity
  apply product_cons_b t806 tb806 ts806 _ _ ts806_sum ts806_parity
  apply product_cons_b t807 tb807 ts807 _ _ ts807_sum ts807_parity
  apply product_cons_b t808 tb808 ts808 _ _ ts808_sum ts808_parity
  apply product_cons_b t809 tb809 ts809 _ _ ts809_sum ts809_parity
  apply product_cons_b t810 tb810 ts810 _ _ ts810_sum ts810_parity
  apply product_cons_b t811 tb811 ts811 _ _ ts811_sum ts811_parity
  apply product_cons_b t812 tb812 ts812 _ _ ts812_sum ts812_parity
  apply product_cons_b t813 tb813 ts813 _ _ ts813_sum ts813_parity
  apply product_cons_b t814 tb814 ts814 _ _ ts814_sum ts814_parity
  apply product_cons_b t815 tb815 ts815 _ _ ts815_sum ts815_parity
  apply product_cons_b t816 tb816 ts816 _ _ ts816_sum ts816_parity
  apply product_cons_b t817 tb817 ts817 _ _ ts817_sum ts817_parity
  apply product_cons_b t818 tb818 ts818 _ _ ts818_sum ts818_parity
  apply product_cons_b t819 tb819 ts819 _ _ ts819_sum ts819_parity
  apply product_cons_b t820 tb820 ts820 _ _ ts820_sum ts820_parity
  apply product_cons_b t821 tb821 ts821 _ _ ts821_sum ts821_parity
  apply product_cons_b t822 tb822 ts822 _ _ ts822_sum ts822_parity
  apply product_cons_b t823 tb823 ts823 _ _ ts823_sum ts823_parity
  apply product_cons_b t824 tb824 ts824 _ _ ts824_sum ts824_parity
  apply product_cons_b t825 tb825 ts825 _ _ ts825_sum ts825_parity
  apply product_cons_b t826 tb826 ts826 _ _ ts826_sum ts826_parity
  apply product_cons_b t827 tb827 ts827 _ _ ts827_sum ts827_parity
  apply product_cons_b t828 tb828 ts828 _ _ ts828_sum ts828_parity
  apply product_cons_b t829 tb829 ts829 _ _ ts829_sum ts829_parity
  apply product_cons_b t830 tb830 ts830 _ _ ts830_sum ts830_parity
  apply product_cons_b t831 tb831 ts831 _ _ ts831_sum ts831_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d768 da768 ds768 _ _ ds768_sum ds768_parity
  apply product_cons_a d769 da769 ds769 _ _ ds769_sum ds769_parity
  apply product_cons_a d770 da770 ds770 _ _ ds770_sum ds770_parity
  apply product_cons_a d771 da771 ds771 _ _ ds771_sum ds771_parity
  apply product_cons_a d772 da772 ds772 _ _ ds772_sum ds772_parity
  apply product_cons_a d773 da773 ds773 _ _ ds773_sum ds773_parity
  apply product_cons_a d774 da774 ds774 _ _ ds774_sum ds774_parity
  apply product_cons_a d775 da775 ds775 _ _ ds775_sum ds775_parity
  apply product_cons_a d776 da776 ds776 _ _ ds776_sum ds776_parity
  apply product_cons_a d777 da777 ds777 _ _ ds777_sum ds777_parity
  apply product_cons_a d778 da778 ds778 _ _ ds778_sum ds778_parity
  apply product_cons_a d779 da779 ds779 _ _ ds779_sum ds779_parity
  apply product_cons_a d780 da780 ds780 _ _ ds780_sum ds780_parity
  apply product_cons_a d781 da781 ds781 _ _ ds781_sum ds781_parity
  apply product_cons_a d782 da782 ds782 _ _ ds782_sum ds782_parity
  apply product_cons_a d783 da783 ds783 _ _ ds783_sum ds783_parity
  apply product_cons_a d784 da784 ds784 _ _ ds784_sum ds784_parity
  apply product_cons_a d785 da785 ds785 _ _ ds785_sum ds785_parity
  apply product_cons_a d786 da786 ds786 _ _ ds786_sum ds786_parity
  apply product_cons_a d787 da787 ds787 _ _ ds787_sum ds787_parity
  apply product_cons_a d788 da788 ds788 _ _ ds788_sum ds788_parity
  apply product_cons_a d789 da789 ds789 _ _ ds789_sum ds789_parity
  apply product_cons_a d790 da790 ds790 _ _ ds790_sum ds790_parity
  apply product_cons_a d791 da791 ds791 _ _ ds791_sum ds791_parity
  apply product_cons_a d792 da792 ds792 _ _ ds792_sum ds792_parity
  apply product_cons_a d793 da793 ds793 _ _ ds793_sum ds793_parity
  apply product_cons_a d794 da794 ds794 _ _ ds794_sum ds794_parity
  apply product_cons_a d795 da795 ds795 _ _ ds795_sum ds795_parity
  apply product_cons_a d796 da796 ds796 _ _ ds796_sum ds796_parity
  apply product_cons_a d797 da797 ds797 _ _ ds797_sum ds797_parity
  apply product_cons_a d798 da798 ds798 _ _ ds798_sum ds798_parity
  apply product_cons_a d799 da799 ds799 _ _ ds799_sum ds799_parity
  apply product_cons_a d800 da800 ds800 _ _ ds800_sum ds800_parity
  apply product_cons_a d801 da801 ds801 _ _ ds801_sum ds801_parity
  apply product_cons_a d802 da802 ds802 _ _ ds802_sum ds802_parity
  apply product_cons_a d803 da803 ds803 _ _ ds803_sum ds803_parity
  apply product_cons_a d804 da804 ds804 _ _ ds804_sum ds804_parity
  apply product_cons_a d805 da805 ds805 _ _ ds805_sum ds805_parity
  apply product_cons_a d806 da806 ds806 _ _ ds806_sum ds806_parity
  apply product_cons_a d807 da807 ds807 _ _ ds807_sum ds807_parity
  apply product_cons_a d808 da808 ds808 _ _ ds808_sum ds808_parity
  apply product_cons_a d809 da809 ds809 _ _ ds809_sum ds809_parity
  apply product_cons_a d810 da810 ds810 _ _ ds810_sum ds810_parity
  apply product_cons_a d811 da811 ds811 _ _ ds811_sum ds811_parity
  apply product_cons_a d812 da812 ds812 _ _ ds812_sum ds812_parity
  apply product_cons_a d813 da813 ds813 _ _ ds813_sum ds813_parity
  apply product_cons_a d814 da814 ds814 _ _ ds814_sum ds814_parity
  apply product_cons_a d815 da815 ds815 _ _ ds815_sum ds815_parity
  apply product_cons_a d816 da816 ds816 _ _ ds816_sum ds816_parity
  apply product_cons_a d817 da817 ds817 _ _ ds817_sum ds817_parity
  apply product_cons_a d818 da818 ds818 _ _ ds818_sum ds818_parity
  apply product_cons_a d819 da819 ds819 _ _ ds819_sum ds819_parity
  apply product_cons_a d820 da820 ds820 _ _ ds820_sum ds820_parity
  apply product_cons_a d821 da821 ds821 _ _ ds821_sum ds821_parity
  apply product_cons_a d822 da822 ds822 _ _ ds822_sum ds822_parity
  apply product_cons_a d823 da823 ds823 _ _ ds823_sum ds823_parity
  apply product_cons_a d824 da824 ds824 _ _ ds824_sum ds824_parity
  apply product_cons_a d825 da825 ds825 _ _ ds825_sum ds825_parity
  apply product_cons_a d826 da826 ds826 _ _ ds826_sum ds826_parity
  apply product_cons_a d827 da827 ds827 _ _ ds827_sum ds827_parity
  apply product_cons_a d828 da828 ds828 _ _ ds828_sum ds828_parity
  apply product_cons_a d829 da829 ds829 _ _ ds829_sum ds829_parity
  apply product_cons_a d830 da830 ds830 _ _ ds830_sum ds830_parity
  apply product_cons_a d831 da831 ds831 _ _ ds831_sum ds831_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 768).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 768).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 768).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 768).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 768).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 768).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 768).take 64) RightCertificate.wideSecond ((tbRows.drop 768).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 768).take 64) RightCertificate.wideFirst ((daRows.drop 768).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block12
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
