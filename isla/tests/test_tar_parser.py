import unittest

from isla.helpers import tree_to_string
from isla.tests.subject_languages import tar


class TestTarParser(unittest.TestCase):
    def Xtest_parse_example_file(self):
        # Does currently not work in CI since file is not located correctly. Does work locally.
        with open('subject_languages/examples/single_file_tar.tar', 'r') as reader:
            content = reader.read()

        assert content is not None

        tar_parser = tar.TarParser()
        parsed_tar_parser = tar_parser.parse(content)[0]
        self.assertEqual(content, tree_to_string(parsed_tar_parser))


if __name__ == '__main__':
    unittest.main()
